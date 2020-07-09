{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DeriveDataTypeable   #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Atoms.Chemistry.Utils.TH.TestTree where
import Control.Monad ( join )
import Control.Monad.Reader
import GHC.Generics
import Data.Data
import Data.Generics.Uniplate.Data
import Data.List ( sortBy, intersect, intercalate, sort, nub, isPrefixOf )
import Data.Maybe ( catMaybes )
import Language.Haskell.TH 

import Debug.Trace


unwrapTopNodeBindings :: Pat -> (Pat, [Name])
unwrapTopNodeBindings (AsP nm p) = (nm:) <$> unwrapTopNodeBindings p
unwrapTopNodeBindings (VarP nm) = (VarP nm, [nm])
unwrapTopNodeBindings p = (p, [])

patToPattern :: Pat -> Pattern
patToPattern (ConP nm pats) = Con nm (patToPattern <$> pats)
patToPattern (UInfixP pl nm pr) = Con nm [patToPattern pl, patToPattern pr]
patToPattern (AsP nm p) = As nm (patToPattern p)
patToPattern (ParensP p) = patToPattern p
patToPattern WildP = Wild
patToPattern (VarP nm) = Var nm
patToPattern _ = error $ "this template does not support that pattern fragment" 

buildTestTree :: [Pattern] -> [Test]
buildTestTree pats = do
  case redundantPatterns pats of
    [] ->
      let ut = (\(i,v,p) -> addBinds p (pruneDeadBranches $ flattenTTests $ testTree i v p))
            <$> (zip3 [1..] (cycle [[]]) pats)


      in trace (unlines (show <$> ut)) ut
    r -> error $ "redundant patterns\n" ++ (unlines (show <$> r))


tag :: [Int] -> Name
tag patindx = mkName ("tag" ++ (intercalate "_" (show <$> patindx)))

res :: [Int] -> Name
res patindx = mkName ("res" ++ (intercalate "_" (show <$> patindx)))

isBoundAsVariantF :: [Int] -> Test -> Bool
isBoundAsVariantF z (Test pth _ _ s f) =
   z == pth || isBoundAsVariantF z s || isBoundAsVariantF z f 
isBoundAsVariantF z (Capture _ _ t) = isBoundAsVariantF z t 
isBoundAsVariantF _ _ = False

class Monad m => Builder m where
  topNodeName :: m Name
  typeName :: m Name
  insertBody  :: Int -> m Body

data TestBuilder =
  TestBuilder {
    topName :: Name
  , tyName :: Name
  , bodies :: [(Int,Body)]
}

instance Builder (Reader TestBuilder) where
  topNodeName = topName <$> ask
  typeName = tyName <$> ask
  insertBody i = do
    mb <- lookup i . bodies <$> ask
    case mb of
      Nothing -> error "insertBody: not found"
      Just bo -> pure bo

writeTestTree :: Name -> Name -> Name -> [Name] -> [(Int,Body)] -> [Test] -> Q [Dec]
writeTestTree funname chname tyvar tnms bodies ct = do 
  node <- newName "node"
  msmn <- newName "maysum"
  msmm <- maysum msmn
  let builder = (TestBuilder node tyvar bodies)
      varbind = runReader (topBoundVar tnms) builder 
      cases  = runReader (sequence (templateTest <$> ct)) builder
  body <- sumbodies node chname msmn cases
  pure [FunD funname [Clause [VarP chname , varbind] body msmm]]

unwrapNormalBs :: [Either Body Body] -> [Exp]
unwrapNormalBs [] = []
unwrapNormalBs ((Right (NormalB e)):rest) = e:(unwrapNormalBs rest)
unwrapNormalBs e = error "this should never happen. normal bodies only at top level"

sumbodies :: Name -> Name -> Name -> [Either Body Body] -> Q Body
sumbodies topnode changed maysumnm bods = do
  let es = unwrapNormalBs bods 
  res <- newName "res"
  so <- newName "so"
  pure (NormalB (CaseE (AppE (VarE maysumnm) (ListE es))
           [Match (ConP (mkName "Nothing") [])
               (NormalB (InfixE (Just (VarE (mkName "pure")))
                                      (VarE (mkName "$"))
                                (Just (AppE (ConE (mkName "Pure")) 
                                      (AppE (ConE (mkName "Molecule"))
                                            (VarE topnode)))))) []
           ,Match (ConP (mkName "Just") [VarP so])
              (NormalB (DoE [NoBindS (AppE (AppE (VarE (mkName "writeSTRef"))
                       (VarE changed)) (ConE (mkName "True")))
                            ,NoBindS (AppE (VarE (mkName "pure")) (VarE so))])) []]))

maysum :: Name -> Q [Dec]
maysum nm = do
   a <- newName "a"
   v <- newName "v"
   r <- newName "r"
   pure [
      SigD nm (AppT (AppT ArrowT (AppT ListT (AppT (ConT (mkName "Maybe")) (VarT a))))
              (AppT (ConT (mkName "Maybe")) (VarT a)))
     ,FunD nm [Clause [ConP (mkName "[]") []] (NormalB (ConE (mkName "Nothing"))) []
              ,Clause [InfixP (ConP (mkName "Just") [VarP v]) (mkName ":") WildP]
                   (NormalB (AppE (ConE (mkName "Just")) (VarE v))) []
              ,Clause [InfixP (ConP (mkName "Nothing") []) (mkName ":") (VarP r)]
                    (NormalB (AppE (VarE nm) (VarE r))) []
              ]
     ]


buildTransformer :: Name -> Name -> Name -> [(Pat,Body)] -> Q [Dec]
buildTransformer funname chname tyvar patbods = do 
  let bodymap = zip [1..] (snd <$> patbods)
      unnamedpats = unwrapTopNodeBindings <$> (fst <$> patbods)
      topnames = nub (sort (join (snd <$> unnamedpats)))
      patterns = patToPattern <$> (fst <$> unnamedpats)
      tests = buildTestTree patterns
  writeTestTree funname chname tyvar topnames (trace (show bodymap) bodymap) (trace (show tests) tests)

topBoundVar :: Builder m => [Name] -> m Pat
topBoundVar [] = do
  nm <- topNodeName
  pure $ AsP nm (ConP (mkName "VariantF") [VarP (tag []), VarP (res [])])
topBoundVar (h:t) = AsP h <$> topBoundVar t

unwrapCaptures :: Test -> (Test, [([Int],Name)])
unwrapCaptures (Capture z n t) = ((z,n):) <$> unwrapCaptures t
unwrapCaptures t@(Test _ _ _ s f) = (t, snd (unwrapCaptures s))
unwrapCaptures e = (e, []) 

testsInside :: Int -> Test -> [[Int]]
testsInside len (Test p _ _ s f) =
  if length p == len
    then p:(testsInside len s ++ testsInside len f)
    else testsInside len s ++ testsInside len f
testsInside len (Capture _ _ t) = testsInside len t
testsInside _ _ = []

safeMaximum :: [Int] -> Maybe Int
safeMaximum [] = Nothing
safeMaximum l = Just $ maximum l

buildMatchArgs :: Int -> [Int] -> [([Int],Name)] -> [[Int]] -> [Pat]
buildMatchArgs numargs pth captures subtests =
  let subtested = zip ((head . reverse) <$> subtests) subtests
      captured  = zip ((\(z,n) -> head (reverse z)) <$> captures) captures
   in case numargs of 
        0 -> []
        _ -> buildArg subtested captured <$> [0..(numargs -1)]
  where buildArg :: [(Int, [Int])] -> [(Int, ([Int], Name))] -> Int -> Pat
        buildArg s c i = 
          case (lookup i s, snd <$> (snd <$> (filter ((==i) . fst) c))) of
             (Nothing, []) -> (ConP (mkName "Pure")
                                     [ ConP (mkName "Molecule") 
                                     [ ConP (mkName "VariantF") 
                                     [VarP (tag (pth ++ [i])), VarP (res (pth ++ [i]))]]])
             (Just ac, []) -> (ConP (mkName "Pure")
                                     [ ConP (mkName "Molecule") 
                                     [ ConP (mkName "VariantF") 
                                     [VarP (tag ac), VarP (res ac)]]])
             (Just ac, vc) -> asPs vc (ConP (mkName "Pure")
                                             [ ConP (mkName "Molecule") 
                                             [ ConP (mkName "VariantF") 
                                             [VarP (tag ac), VarP (res ac)]]])
             (Nothing, vc) -> asPs (tail vc) (VarP (head vc))

asPs :: [Name] -> (Pat -> Pat)
asPs [] = id
asPs (h:t) = AsP h . (asPs t)


templateMatch :: Builder m
              => Int -> [Int] -> Name -> [([Int], Name)] -> [[Int]] -> Either Body Body -> m Body
templateMatch i pth con captures subtests (Right body) = 
  pure (NormalB (CaseE (VarE (res pth))
          [Match (ConP con (buildMatchArgs i pth captures subtests)) body []]))
templateMatch i pth con captures subtests (Left body) = 
  pure (NormalB (CaseE (VarE (res pth))
          [Match (ConP con (buildMatchArgs i pth captures subtests)) body []
          ,Match WildP (NormalB (ConE (mkName "Nothing"))) [] 
          ]))


templateTest :: Builder m => Test -> m (Either Body Body)
templateTest t =
  case unwrapCaptures t of
    (Test pth cnm i s f, capt) -> do
      let z = (length pth) + 1
          inside = filter (\p -> pth `isPrefixOf` p) (testsInside z s)
          captsof = filter (\c -> length (fst c) == z && pth `isPrefixOf` (fst c)) capt
      tnm <- typeName
      succBranch <- templateMatch i pth cnm captsof inside =<< templateTest s
      failBranch <- templateTest f 
      case failBranch of
         Right failBranchNorm ->
             pure $ Right (NormalB (CaseE (AppE (AppE (VarE (mkName "testEquality")) 
                                                   (VarE (tag pth))) 
                                  (AppTypeE (VarE (mkName "fromSides")) 
                                  (AppT (AppT (ConT (mkName "Locate")) (ConT cnm)) 
                                                          (VarT tnm))))
                          [Match (ConP (mkName "Just") [ConP (mkName "Refl") []])
                                                  succBranch []
                          ,Match WildP failBranchNorm []
                          ]
                    ))
         _ -> error "this should never happen"
    (Accept [b], _) -> do
      bod <- insertBody b 
      case bod of
         GuardedB _ -> pure $ Left bod
         _ -> pure $ Right bod
    (Accept [], []) -> pure $ Right (NormalB (ConE (mkName "Nothing")))
    e -> error (show e)



data Pattern = Con Name [Pattern] | Var Name | Wild | As Name Pattern 
  deriving ( Show, Data, Generic, Ord )

instance Eq Pattern where
  (==) (Con l pl) (Con r pr) = l == r && pl == pr
  (==) (As _ p) q = p == q
  (==) p (As _ q) = p == q
  (==) (Con _ _) _ = False
  (==) _ (Con _ _) = False
  (==) _ _ = True

redundantPatterns :: [Pattern] -> [Pattern]
redundantPatterns pats = [p | p <- pats, length (filter (==p) pats) > 1]


binds :: Pattern -> [Name]
binds p = [ v | Var v <- universe p] ++ [ v | As v _ <- universe p]

-- |    Type equality tests can pass or fail 
-- they test a path to a        |     |
--                 | constructor|
--                 |    |       |     |
--                 |    |       |
--                 v    V       v     v
data Test = Test [Int] Name Int Test Test 
          | TTest [Test] 
          | Capture [Int] Name Test -- Int is a path into a pattern
          | Accept [Int] --Int is a Body tag
  deriving ( Show, Eq)

joinAllOrNothing :: Eq a => [Maybe [a]] -> Maybe [a]
joinAllOrNothing ml = if any (==Nothing) ml then Nothing else Just (join (catMaybes ml))        

indexPatternC :: Pattern -> [Int] -> Maybe Name
indexPatternC (Con s _) [] = Just s
indexPatternC (Con s ps) (h:r) =
  if length ps > h then indexPatternC (ps!!h) r else Nothing 
indexPatternC (As _ p) l = indexPatternC p l
indexPatternC _ _ = Nothing

indexPatternV :: Pattern -> [Int] -> Maybe Name
indexPatternV (Con s ps) [i] =
  if length ps > i
    then case (ps!!i) of
           Var v -> Just v
           _ -> Nothing
     else Nothing 
indexPatternV _ _ = Nothing

boundAt :: Pattern -> [Int] -> [(Name,[Int])]
boundAt (Con s ps) [] = join ((\(i,p) -> case p of
                                            Var v -> [(v,[i])]
                                            As v _ -> [(v,[i])] 
                                            _ -> []) <$> (zip [0..] ps))
boundAt (Con s ps) (h:r) =
  if length ps > h
    then ((h:) <$>) <$> boundAt (ps!!h) r
    else error "boundAt"
boundAt (As _ p) l = boundAt p l
boundAt _ _ = error "boundAt"

boundAtT :: Pattern -> [Int] -> [Test -> Test]
boundAtT p pth = (\(v, p) -> Capture p v) <$> boundAt p pth 


-- | TODO return Left with error of bindings clash
runTest :: Test -> Pattern -> Maybe (Int,[Name])
runTest (Capture pth v t) p =((v:) <$>) <$> runTest t p
runTest (Test pth t _ s f) p =
  case indexPatternC p pth of
    Nothing -> runTest f p
    Just so -> if so == t then runTest s p else runTest f p
runTest (Accept [a]) _ = Just (a,[]) 
runTest _ _ = Nothing

addBinds :: Pattern -> Test -> Test
addBinds p (Capture i c t) = Capture i c (addBinds p t)
addBinds p (Test pth t i s f) = 
  case indexPatternC p pth of
    Nothing -> Test pth t i s (addBinds p f)
    Just so -> if so == t 
                 then Test pth t i (foldl (\a b -> b a) (addBinds p s) (boundAtT p pth)) f
                  else Test pth t i s (addBinds p f)
addBinds _ e = e

testTree :: Int -> [Int] -> Pattern -> Test
testTree i pth (Con c []) = Test pth c 0 (Accept [i]) (Accept [])
testTree i pth (Con c [inner]) = Test pth c 1 (testTree i (pth ++ [0]) inner) (Accept [])
testTree i pth (Con c inners) =
   Test pth c (length inners) (TTest (uncurry (testTree i)
   <$> (zip ((\z -> pth ++ [z]) <$> [0..]) inners))) (Accept [])
testTree i pth (As _ p) = testTree i pth p
testTree i pth (Var _) = Accept [i]
testTree i pth Wild = Accept [i]


flattenTTests :: Test -> Test
flattenTTests (Capture pth v t) = Capture pth v (flattenTTests t)
flattenTTests (Test i c nrgs s f) = Test i c nrgs (flattenTTests s) (flattenTTests f)
flattenTTests (Accept k) = Accept k
flattenTTests (TTest tsts) = foldTTests tsts

foldTTests :: [Test] -> Test
foldTTests [] = error ""
foldTTests [Accept a] = Accept a
foldTTests [Test i c nrgs s f] = Test i c nrgs s f
foldTTests [(h@(Test li lc nrgsl ls lf)),(n@(Test ri rc nrgsr rs rf))] =
    intersectTests (Test li lc nrgsl (flattenTTests ls) (flattenTTests lf))
                   (Test ri rc nrgsr (flattenTTests rs) (flattenTTests rf))
foldTTests ((Test i c nrgs s f):r) =
    intersectTests (Test i c nrgs (flattenTTests s) (flattenTTests f)) (foldTTests r)
foldTTests ((Accept as):t:r) = foldTTests ((applyTestIntersect as t):r)
foldTTests e = error (show e)

applyTestIntersect :: [Int] -> Test -> Test
applyTestIntersect with (Test i c n s f) = Test i c n (applyTestIntersect with s)
                                                      (applyTestIntersect with f) 
applyTestIntersect with (Accept r) = Accept (with `intersect` r)
applyTestIntersect with (Capture pth c t) = Capture pth c (applyTestIntersect with t)
applyTestIntersect with (TTest tsts) = TTest (applyTestIntersect with <$> tsts)

intersectTests :: Test -> Test -> Test
intersectTests (Test i c n s f) t = Test i c n (intersectTests s t) (intersectTests f t)
intersectTests (Capture pth s i) t = Capture pth s (intersectTests i t)
intersectTests (Accept a) t = applyTestIntersect a t

testAccepts :: Test -> [Int]
testAccepts (Accept a) = a
testAccepts (Capture _ _ t) = testAccepts t
testAccepts (Test _ _ _ s f) = testAccepts s ++ testAccepts f
testAccepts (TTest tsts) = join (testAccepts <$> tsts)

pruneDeadBranches :: Test -> Test
pruneDeadBranches t =
    case testAccepts t of
        [] -> Accept [] 
        _ -> case t of
               Accept a -> Accept a
               Test i c n s f ->
                  case testAccepts s of
                    [] -> pruneDeadBranches f
                    _ -> Test i c n (pruneDeadBranches s) (pruneDeadBranches f)
               Capture pth s t -> Capture pth s (pruneDeadBranches t)
               TTest tsts -> TTest (filter (/= (Accept [])) (pruneDeadBranches <$> tsts))



