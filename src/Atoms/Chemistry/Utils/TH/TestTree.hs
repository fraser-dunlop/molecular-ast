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

buildTestTree :: [Pattern] -> Test
buildTestTree pats = do
  let bindVars = \t -> foldl (\a b -> b a) t (addBinds <$> pats)
  case redundantPatterns pats of
    [] ->
      let ut = bindVars
             $ pruneDeadBranches
             $ flattenTTests 
             $ unifyTestList (((\(i,v,p) -> testTree i v p)
            <$> (zip3 [1..] (cycle [[]]) pats)))
          matches = runTest ut <$> pats
          bindsof = binds <$> pats
      in if all id (zipWith (==) (Just <$> [1..]) ((fst <$>) <$> matches))
           then trace "All patterns mapped to correct bodies" ut 
           else error "Some pattern was not mapped to the correct body"
    r -> error $ "redundant patterns\n" ++ (unlines (show <$> r))


tag :: [Int] -> Name
tag patindx = mkName ("tag" ++ (intercalate "_" (show <$> patindx)))

res :: [Int] -> Name
res patindx = mkName ("res" ++ (intercalate "_" (show <$> patindx)))

isBoundAsVariantF :: [Int] -> Test -> Bool
isBoundAsVariantF z (Test pth _ s f) =
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

writeTestTree :: Name -> Name -> Name -> [Name] -> [(Int,Body)] -> Test -> Q [Dec]
writeTestTree funname chname tyvar tnms bodies ct = do 
  node <- newName "node"
  let builder = (TestBuilder node tyvar bodies)
      varbind = runReader (topBoundVar tnms) builder 
      body    = runReader (templateTest ct) builder
  pure [FunD funname [Clause [VarP chname , varbind] body []]]


buildTransformer :: Name -> Name -> Name -> [(Pat,Body)] -> Q [Dec]
buildTransformer funname chname tyvar patbods = do 
  let bodymap = zip [1..] (snd <$> patbods)
      unnamedpats = unwrapTopNodeBindings <$> (fst <$> patbods)
      topnames = nub (sort (join (snd <$> unnamedpats)))
      patterns = patToPattern <$> (fst <$> unnamedpats)
      test = buildTestTree patterns
  writeTestTree funname chname tyvar topnames (trace (show bodymap) bodymap) (trace (show test) test)

topBoundVar :: Builder m => [Name] -> m Pat
topBoundVar [] = do
  nm <- topNodeName
  pure $ AsP nm (ConP (mkName "VariantF") [VarP (tag []), VarP (res [])])
topBoundVar (h:t) = AsP h <$> topBoundVar t

unwrapCaptures :: Test -> (Test, [([Int],Name)])
unwrapCaptures (Capture z n t) = ((z,n):) <$> unwrapCaptures t
unwrapCaptures t@(Test _ _ s f) = (t, snd (unwrapCaptures s))
unwrapCaptures e = (e, []) 

testsInside :: Int -> Test -> [[Int]]
testsInside len (Test p _ s f) =
  if length p == len
    then p:(testsInside len s ++ testsInside len f)
    else testsInside len s ++ testsInside len f
testsInside len (Capture _ _ t) = testsInside len t
testsInside _ _ = []

safeMaximum :: [Int] -> Maybe Int
safeMaximum [] = Nothing
safeMaximum l = Just $ maximum l

buildMatchArgs :: [([Int],Name)] -> [[Int]] -> [Pat]
buildMatchArgs captures subtests =
  let subtested = zip ((head . reverse) <$> subtests) subtests
      captured  = zip ((\(z,n) -> head (reverse z)) <$> captures) captures
      numargs   = safeMaximum ((fst <$> subtested) ++ (fst <$> captured))
   in case numargs of 
        Nothing -> []
        Just so -> buildArg subtested captured <$> [0..so]
  where buildArg :: [(Int, [Int])] -> [(Int, ([Int], Name))] -> Int -> Pat
        buildArg s c i = 
          case (lookup i s, snd <$> (snd <$> (filter ((==i) . fst) c))) of
             (Nothing, []) -> error "buildArg"
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
              => [Int] -> Name -> [([Int], Name)] -> [[Int]] -> Body -> m Body
templateMatch pth con captures subtests body = 
  pure (NormalB (CaseE (VarE (res pth))
          [Match (ConP con (buildMatchArgs captures subtests)) body []]))

templateTest :: Builder m => Test -> m Body
templateTest t =
  case unwrapCaptures t of
    (Test pth cnm s f, capt) -> do
      let z = (length pth) + 1
          inside = filter (\p -> pth `isPrefixOf` p) (testsInside z s)
          captsof = filter (\c -> length (fst c) == z && pth `isPrefixOf` (fst c)) capt
      tnm <- typeName
      succBranch <- templateMatch pth cnm captsof inside =<< templateTest s
      failBranch <- templateTest f 
      pure (NormalB (CaseE (AppE (AppE (VarE (mkName "testEquality")) (VarE (tag pth))) 
                           (AppTypeE (VarE (mkName "fromSides")) 
                           (AppT (AppT (ConT (mkName "Locate")) (ConT cnm)) (VarT tnm))))
                   [Match (ConP (mkName "Just") [ConP (mkName "Refl") []]) succBranch []
                   ,Match WildP failBranch []
                   ]
             ))
    (Accept [b], _) -> do
      insertBody b
    (Accept [], []) -> do 
      top <- topNodeName
      pure (NormalB (AppE (VarE (mkName "pure"))
                    (AppE (ConE (mkName "Pure"))
                    (AppE (ConE (mkName "Molecule"))
                    (VarE top)))))
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
data Test = Test [Int] Name Test Test 
          | TTest [Test] 
          | Capture [Int] Name Test -- Int is a path into a pattern
          | Accept [Int] --Int is a Body tag
  deriving ( Show, Eq)

testSize :: Test -> Int
testSize (Test _ _ s f) = 1 + testSize s + testSize f
testSize (TTest tests) = sum (testSize <$> tests)
testSize (Capture _ _ t) = testSize t
testSize _ = 0

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
runTest (Test pth t s f) p =
  case indexPatternC p pth of
    Nothing -> runTest f p
    Just so -> if so == t then runTest s p else runTest f p
runTest (Accept [a]) _ = Just (a,[]) 
runTest _ _ = Nothing

addBinds :: Pattern -> Test -> Test
addBinds p (Capture i c t) = Capture i c (addBinds p t)
addBinds p (Test pth t s f) = 
  case indexPatternC p pth of
    Nothing -> Test pth t s (addBinds p f)
    Just so -> if so == t 
                 then Test pth t (foldl (\a b -> b a) (addBinds p s) (boundAtT p pth)) f
                  else Test pth t s (addBinds p f)
addBinds _ e = e

testTree :: Int -> [Int] -> Pattern -> Test
testTree i pth (Con c []) = Test pth c (Accept [i]) (Accept [])
testTree i pth (Con c [inner]) = Test pth c (testTree i (pth ++ [0]) inner) (Accept [])
testTree i pth (Con c inners) =
   Test pth c (TTest (uncurry (testTree i)
   <$> (zip ((\z -> pth ++ [z]) <$> [0..]) inners))) (Accept [])
testTree i pth (As _ p) = testTree i pth p
testTree i pth (Var _) = Accept [i]
testTree i pth Wild = Accept [i]


unifyTests :: Test -> Test -> Test
unifyTests (Capture pth v tl) tr = Capture pth v (unifyTests tl tr)
unifyTests tl (Capture pth v tr) = Capture pth v (unifyTests tl tr)
unifyTests (Test i conl sl fl) tr@(Test j conr sr fr)
    | i == j && conl == conr = Test i conl (unifyTests sl sr) (unifyTests fl fr)
    | otherwise = Test i conl sl (unifyTests fl tr)
unifyTests (Test i conl sl fl) tt@(TTest _) = Test i conl sl (unifyTests fl tt) 
unifyTests tt@(TTest _) (Test i conr sr fr) = Test i conr sr (unifyTests fr tt) 
unifyTests (TTest ttl) (TTest ttr) =
   if length ttl /= length ttr
     then error "patterns do not have the same arity"
     else TTest (zipWith unifyTests ttl ttr)
unifyTests (Accept l) (Accept r) = Accept (l ++ r)
unifyTests a@(Accept _) (Test i c s f) = Test i c s (unifyTests a f)
unifyTests (Test i c s f) a@(Accept _) = Test i c s (unifyTests a f)
unifyTests l r = error $ "unify failure\n" ++ (show l) ++ "\n" ++ (show r) 

unifyTestList :: [Test] -> Test
unifyTestList [] = (Accept []) 
unifyTestList [s] = s
unifyTestList l =
  case sortBy (\a b -> testSize a `compare` testSize b) l of
    (h:t) -> foldl (\a b -> unifyTests a b) h t


flattenTTests :: Test -> Test
flattenTTests (Capture pth v t) = Capture pth v (flattenTTests t)
flattenTTests (Test i c s f) = Test i c (flattenTTests s) (flattenTTests f)
flattenTTests (Accept k) = Accept k
flattenTTests (TTest tsts) = foldTTests tsts

foldTTests :: [Test] -> Test
foldTTests [] = error ""
foldTTests [Accept a] = Accept a
foldTTests [Test i c s f] = Test i c s f
foldTTests [(h@(Test li lc ls lf)),(n@(Test ri rc rs rf))] =
    intersectTests (Test li lc (flattenTTests ls) (flattenTTests lf))
                   (Test ri rc (flattenTTests rs) (flattenTTests rf))
foldTTests ((Test i c s f):r) =
    intersectTests (Test i c (flattenTTests s) (flattenTTests f)) (foldTTests r)
foldTTests e = error (show e)

applyTestIntersect :: [Int] -> Test -> Test
applyTestIntersect with (Test i c s f) = Test i c (applyTestIntersect with s)
                                                  (applyTestIntersect with f) 
applyTestIntersect with (Accept r) = Accept (with `intersect` r)
applyTestIntersect with (Capture pth c t) = Capture pth c (applyTestIntersect with t)
applyTestIntersect with (TTest tsts) = TTest (applyTestIntersect with <$> tsts)

intersectTests :: Test -> Test -> Test
intersectTests (Test i c s f) t = Test i c (intersectTests s t) (intersectTests f t)
intersectTests (Capture pth s i) t = Capture pth s (intersectTests i t)
intersectTests (Accept []) t = t
intersectTests (Accept a) t = applyTestIntersect a t

testAccepts :: Test -> [Int]
testAccepts (Accept a) = a
testAccepts (Capture _ _ t) = testAccepts t
testAccepts (Test _ _ s f) = testAccepts s ++ testAccepts f
testAccepts (TTest tsts) = join (testAccepts <$> tsts)

pruneDeadBranches :: Test -> Test
pruneDeadBranches t =
    case testAccepts t of
        [] -> Accept [] 
        _ -> case t of
               Accept a -> Accept a
               Test i c s f ->
                  case testAccepts s of
                    [] -> pruneDeadBranches f
                    _ -> Test i c (pruneDeadBranches s) (pruneDeadBranches f)
               Capture pth s t -> Capture pth s (pruneDeadBranches t)
               TTest tsts -> TTest (filter (/= (Accept [])) (pruneDeadBranches <$> tsts))



