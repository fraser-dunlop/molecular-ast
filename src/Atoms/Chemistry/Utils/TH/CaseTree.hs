module Atoms.Chemistry.Utils.TH.CaseTree where
import Language.Haskell.TH 
import Control.Monad ( join )
import Debug.Trace
import Control.Monad.State
import Control.Monad
import Data.List (sort, nub, sortBy)


data BoundVar = CapturedAs Name BoundVar | BoundVar Name Name deriving (Eq, Show)

rebindVar :: (Name, Name) -> (Name, Name)-> BoundVar -> BoundVar
rebindVar from to (CapturedAs s b) = CapturedAs s (rebindVar from to b)
rebindVar from to (BoundVar tag res) =
   if (tag, res) == from
     then let (tag, res) = to
            in BoundVar tag res 
       else BoundVar tag res

isVar :: (Name, Name) -> BoundVar -> Bool
isVar i (CapturedAs s b) = isVar i b
isVar i (BoundVar tag res) = i == (tag, res)

inVar :: BoundVar -> (Name, Name) 
inVar (CapturedAs s b) = inVar b
inVar (BoundVar tag res) = (tag, res)

unifyBV :: BoundVar -> BoundVar -> Bool 
unifyBV a b = inVar a == inVar b

captureList :: BoundVar -> [Name]
captureList (BoundVar _ _) = []
captureList (CapturedAs s b) = nub (sort (s:(captureList b)))

mergeBV :: BoundVar -> BoundVar -> BoundVar
mergeBV l r =
  let cl = captureList l
      cr = captureList r
      (tag, res) = (inVar l)
   in foldr CapturedAs (BoundVar tag res) (nub (sort (cl ++ cr)))
      

captureVar :: Name -> (Name, Name) -> BoundVar -> BoundVar
captureVar as capt b = if isVar capt b then CapturedAs as b else b 

data CaseTree a = ProofExp Pat BoundVar [CaseTree a] [CaseTree a]
                | CaseExp BoundVar [CaseTree a] 
                | CaseMatch Pat [BoundVar] [CaseTree a] 
                | CaseBody a    
  deriving Show

addDefaultToGuardedBodies :: CaseTree [Body] -> CaseTree [Body] -> CaseTree [Body]
addDefaultToGuardedBodies defolt (CaseExp bve [m@(CaseMatch _ _ [CaseBody [GuardedB _]])])
    = CaseExp bve [m, CaseMatch WildP [] [defolt]]
addDefaultToGuardedBodies defolt (CaseExp bv ct)
    = CaseExp bv (addDefaultToGuardedBodies defolt <$> ct) 
addDefaultToGuardedBodies defolt (ProofExp p bv cts ctf)
    = ProofExp p bv (addDefaultToGuardedBodies defolt <$> cts) 
                    (addDefaultToGuardedBodies defolt <$> ctf) 
addDefaultToGuardedBodies defolt (CaseMatch p bvs ct)
    = CaseMatch p bvs (addDefaultToGuardedBodies defolt <$> ct) 
addDefaultToGuardedBodies _ e = e


isBoundAsVariantF :: BoundVar -> CaseTree [a] -> Bool
isBoundAsVariantF (BoundVar _ _) _ = True
isBoundAsVariantF b (ProofExp _ bv cts ctf) = (unifyBV b bv || any id (isBoundAsVariantF b <$> cts)) || (unifyBV b bv || any id (isBoundAsVariantF b <$> ctf))
isBoundAsVariantF b (CaseExp bv cts) = unifyBV b bv || any id (isBoundAsVariantF b <$> cts) 
isBoundAsVariantF b (CaseMatch _ _ cts) = any id (isBoundAsVariantF b <$> cts) 
isBoundAsVariantF b _ = False


sortCases :: [CaseTree [a]] -> [CaseTree [a]]
sortCases = sortBy (\l r -> case (l,r) of
                              (CaseMatch WildP _ _,_) -> GT 
                              (CaseMatch pl _ _, CaseMatch pr _ _) -> pr `compare` pl
                              (CaseExp _ _,_) -> LT
                              (CaseBody _,_) -> GT
                              (ProofExp _ _ _ _, _) -> LT)

mergeMatches :: [CaseTree [a]] -> [CaseTree [a]]
mergeMatches  [] = []
mergeMatches (a:[]) = [a]
mergeMatches (a:b:r) =
  case mergeCaseTrees a b of
    [o] -> mergeMatches (o:r)
    [a',b'] -> a':(mergeMatches (b':r))
    _ -> error "mergeMatches"
  
chainFold :: a -> [a -> a] -> a
chainFold a [] = a
chainFold a (h:t) = chainFold (h a) t



proofChain :: [CaseTree [a]] -> Maybe (CaseTree [a])
proofChain [p@(ProofExp _ _ _ _)] = Just p
proofChain ((ProofExp pt bv su _):(p@(CaseMatch WildP _ _)):[]) = Just (ProofExp pt bv su [p])
proofChain ((ProofExp pt bv su _):p:[]) = Just (ProofExp pt bv su [p])
proofChain (h@(ProofExp _ _ _ _):p:ps) =
  case proofChain (p:ps) of
    Nothing -> Nothing
    Just s -> proofChain [h, s]
proofChain _ = Nothing 

promotePatterns :: BoundVar -> CaseTree [a] -> (CaseTree [a] -> CaseTree [a])
promotePatterns _ (CaseExp bv tr) =
  \d -> let could_be_proofs = (\p -> p d) <$> (promotePatterns bv <$> tr)
          in case proofChain (sortCases could_be_proofs) of
            Nothing -> CaseExp bv could_be_proofs
            Just pc -> CaseExp bv [pc] 
promotePatterns bv (CaseMatch con@(ConP _ _) bvs tr) =
   \d -> ProofExp con bv [CaseExp bv [CaseMatch con bvs
                              [(chainFold d (promotePatterns bv <$> tr))]]]
                         [ d ]
promotePatterns bu (CaseMatch p bv ct) = \d -> CaseMatch p bv ((\p -> p d) <$> (promotePatterns bu <$> ct))
promotePatterns _ (CaseBody a) = \_ -> CaseBody a
promotePatterns _ _ = error "promotePatterns" 



mergeCaseTrees :: CaseTree [a] -> CaseTree [a] -> [CaseTree [a]]
mergeCaseTrees (CaseExp bvl trl) (CaseExp bvr trr) =
    [CaseExp bvl (mergeMatches (sortCases (trl ++ (traverseBoundVars (\b -> if unifyBV b bvr then rebindVar (inVar bvr) (inVar bvl) b else b) <$> trr))))]
mergeCaseTrees l@(CaseMatch consl bvsl trl) r@(CaseMatch consr bvsr trr) =
    if consl == consr   
      then 
        let rebindr = zipWith (\bvl bvr -> (\b -> if unifyBV b bvr then rebindVar (inVar bvr) (inVar bvl) b else b)) bvsl bvsr
         in [CaseMatch consl (zipWith mergeBV bvsl bvsr) (mergeMatches (sortCases (trl ++ (traverseBVList rebindr <$> trr))))]
      else [l,r]
mergeCaseTrees (CaseBody l) (CaseBody r) = [CaseBody (l ++ r)]
mergeCaseTrees (CaseExp bv ct) r@(CaseBody i) =
   [CaseExp bv (mergeMatches (sortCases ((CaseMatch WildP [] [r]):ct)))]
mergeCaseTrees l@(CaseBody _) (CaseExp bv ct) =
   [CaseExp bv (mergeMatches (sortCases ((CaseMatch WildP [] [l]):ct)))]


class Monad m => NewVarM m where
  newVar :: m BoundVar

instance NewVarM Q where
  newVar = do
    tag <- newName "tag"
    res <- newName "res"
    pure (BoundVar tag res) 

liftCase :: NewVarM m => a -> BoundVar -> Pat -> m (CaseTree [a])
liftCase i bv p = do
    d <- liftCase' bv p
    case d of
      Right ct -> pure (ct (CaseBody [i]))
      Left rma -> pure $ CaseExp (rma bv) []
  where
    liftCase' :: NewVarM m => BoundVar -> Pat
              -> m (Either (BoundVar -> BoundVar) (CaseTree [a] -> CaseTree [a]))
    liftCase' bv (UInfixP pl nm pr) = liftCase' bv (ConP nm [pl,pr])
    liftCase' bv (AsP nm p) = liftCase' (CapturedAs nm bv) p  
    liftCase' bv (ParensP p) = liftCase' bv p
    liftCase' bv WildP = pure $ Right (\d -> CaseExp bv [(CaseMatch WildP [] [d])]) 
    liftCase' bv (VarP s) = pure $ Left (captureVar s (inVar bv)) 
    liftCase' bv (ConP s pats) = do
       cases <- sequence ((\p -> do
                              nbv <- newVar
                              c <- liftCase' nbv p
                              pure (nbv, c)) <$> pats)
       let captures = join (map (\b -> case b of
                                    (_,Left ca) -> [ca]
                                    _ -> []) cases)
       let casetrees = join (map (\b -> case b of
                                    (_,Right ct) -> [ct]
                                    _ -> []) cases)
       case casetrees of
         [] -> pure $ Right (\d -> traverseBVList captures
                    $ CaseExp bv [(CaseMatch (ConP s []) (fst <$> cases) [d])]) 
         _ -> pure $ Right (\d -> traverseBVList captures
                   $ CaseExp bv [(CaseMatch (ConP s []) (fst <$> cases) [chainFold d casetrees])])
    liftCase' _ p = error $ "unsupported pattern fragment " ++ show p

traverseBVList :: [BoundVar -> BoundVar] -> CaseTree a -> CaseTree a
traverseBVList [] ct = ct
traverseBVList (h:t) ct = traverseBVList t (traverseBoundVars h ct)

traverseBoundVars :: (BoundVar -> BoundVar) -> CaseTree a -> CaseTree a
traverseBoundVars f (CaseExp bv tr) = CaseExp (f bv) (traverseBoundVars f <$> tr)
traverseBoundVars f (CaseMatch s bvs tr) = CaseMatch s (f <$> bvs) (traverseBoundVars f <$> tr)
traverseBoundVars _ c = c

buildCaseTree :: [(Pat,Body)] -> Q (CaseTree [Body])
buildCaseTree patbods = do
  topvar <- newVar 
  cts <- sequence ((\(p,n) -> liftCase n topvar p) <$> patbods) 
  case mergeMatches (sortCases cts) of
    [s] -> pure s
    _ -> error "case tree build failed"
  

topBoundVar :: BoundVar -> Q (Name, Pat)
topBoundVar (CapturedAs nm b) = do
   (node, v) <- topBoundVar b
   pure (node, AsP nm v)
topBoundVar (BoundVar tag res) = do
  node <- newName "node"
  pure (node, AsP node (ConP (mkName "VariantF") [VarP tag, VarP res])) 

innerBoundVar :: BoundVar -> Q Pat
innerBoundVar bv = do
  b <- topBoundVar bv
  pure (ConP (mkName "Pure") [ ConP (mkName "Molecule") [snd b]])

boundAs :: BoundVar -> Pat
boundAs (CapturedAs nm (BoundVar _ _)) = (VarP nm)
boundAs (CapturedAs nm cas) = (AsP nm (boundAs cas))
boundAs _ = error "boundAs"


defaultCase :: Name -> CaseTree [Body]
defaultCase nm = CaseBody [(NormalB (AppE (VarE (mkName "pure"))
                                               (AppE (ConE (mkName "Pure"))
                                               (AppE (ConE (mkName "Molecule"))
                                               (VarE nm)))))]

templateCaseTree :: Name -> CaseTree [Body] -> Q (Pat, Body)
templateCaseTree t c@(CaseExp bv tr) = do 
  (node, topv) <- topBoundVar bv
  ct <- case addDefaultToGuardedBodies (defaultCase node) (promotePatterns bv c (defaultCase node)) of
          e@(CaseExp _ tr) -> inCaseTree t tr
          _ -> error "templateCaseTree."
  pure (topv, ct)
templateCaseTree _ _ = error "templateCaseTree"

inCaseTree :: Name -> [CaseTree [Body]] -> Q Body 
inCaseTree t [(ProofExp (ConP nm []) bv su fa)] = do 
  let (tag, res) = inVar bv
  suc <- inCaseTree t su 
  fai <- inCaseTree t fa
  pure (NormalB (CaseE (AppE (AppE (VarE (mkName "testEquality")) (VarE tag)) 
                (AppTypeE (VarE (mkName "fromSides")) 
                (AppT (AppT (ConT (mkName "Locate")) (ConT nm)) (VarT t))))
        [Match (ConP (mkName "Just") [ConP (mkName "Refl") []]) suc []
        ,Match WildP fai []
        ]
    ))
inCaseTree t [CaseExp _ [p@(ProofExp _ _ _ _)]] = inCaseTree t [p] 
inCaseTree t [CaseExp bv tr] =  do
  let (_, res) = inVar bv
  matches <- matchTree t tr
  pure (NormalB (CaseE (VarE res) matches)) 
inCaseTree t [CaseBody [bod]] = pure bod 
inCaseTree t [CaseMatch WildP _ [CaseExp _ [p@(ProofExp _ _ _ _)]]] = inCaseTree t [p] 
inCaseTree _ e = error $ "inCaseTree: unexpected" ++ show e

prettyCaseTree ind (ProofExp c b trs trf) =
   (replicate ind ' ') ++ "proof " ++ show c ++ " ~ " ++ show b ++ " of\n"
   ++ (replicate (ind + 2) ' ') ++ "Just Refl ->\n" 
   ++ join (prettyCaseTree (ind + 4) <$> trs)
   ++ (replicate (ind + 2) ' ') ++ "_ ->\n" 
   ++ join (prettyCaseTree (ind + 2) <$> trf)

prettyCaseTree ind (CaseExp b tr) = (replicate ind ' ') ++ "case " ++ show b ++ " of\n" ++ join (prettyCaseTree (ind + 2) <$> tr)
prettyCaseTree ind (CaseMatch s bs tr) = (replicate ind ' ') ++ show s ++ " " ++ unwords (show <$> bs) ++ "->\n" ++ join (prettyCaseTree (ind + 2) <$> tr) 
prettyCaseTree ind (CaseBody is) = (replicate ind ' ') ++ show is ++ "\n"




matchTree :: Name -> [CaseTree [Body]] -> Q [Match] 
matchTree _ [] = pure []
matchTree t ((CaseMatch (ConP nm []) bvs [CaseBody [body]]):rest) = do
    following <- matchTree t rest
    let ibvs = (boundAs <$> bvs)
    pure ((Match (ConP nm (ibvs)) body []):following)
matchTree t ((CaseMatch (ConP nm []) bvs tr):rest) = do
    cont <- inCaseTree t tr
    following <- matchTree t rest
    if any id ((\b -> any id (isBoundAsVariantF b <$> (tr ++ rest))) <$> bvs)
      then do
        ibvs <- sequence (innerBoundVar <$> bvs)
        pure ((Match (ConP nm (ibvs)) cont []):following)
      else do
        let ibvs = (boundAs <$> bvs)
        pure ((Match (ConP nm (ibvs)) cont []):following)
matchTree t ((CaseMatch WildP _ tr):rest) = do
    cont <- inCaseTree t tr
    following <- matchTree t rest
    pure ((Match WildP cont []):following)
matchTree t ((CaseMatch (ConP _ [ConP _ []]) _ tr):rest) = do
    cont <- inCaseTree t tr
    following <- matchTree t rest
    pure ((Match (ConP (mkName "Just") [ConP (mkName "Refl") []]) cont []):following)
matchTree _ e = error $ "matchTree\n\n\n " ++ (unlines (prettyCaseTree 0 <$> e)) 


