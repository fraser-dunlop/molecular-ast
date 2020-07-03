{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
module Atoms.Chemistry.Utils.TH where

import Language.Haskell.TH
import Atoms.Elements.PropCalc.Not
import Atoms.Molecule.AST
import Data.Type.Equality
import Hyper
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF
import Data.STRef
import Control.Monad.ST

import qualified GHC.Base
import qualified Hyper.Type.Pure 
import qualified Atoms.Molecule.AST
import Language.Haskell.Meta.Parse
import Language.Haskell.TH.Quote

import Control.Monad (join)
import Data.List (sort,nub)
import Data.Char (toUpper)
import Data.List (isPrefixOf)
import Debug.Trace 

class ( HasF Not t
      , ForAllIn Functor t
      , ForAllIn Foldable t
      , ForAllIn Traversable t
      , Follow (Locate Not t) t ~ Not 
      , FromSides (Locate Not t)
      ) => DoubleNegation t where
    doubleNegation ::  STRef s Bool
                   -> VariantF t (Pure # Molecule (VariantF t))
                   -> ST s (Pure # Molecule (VariantF t))




test :: IO ()
test = do
   printClassDec
   putStrLn ""
   printInstanceDec
   putStrLn ""
   let fundef1 = "aFunction changed (Not (Not v)) = v\naFunction changed (And (Variable v) (Variable q)) | v == q = Variable v\naFunction changed (Not v) = v\naFunction changed (Not _) = undefined"
   let Right [dec] = parseDecs fundef1 
   print dec
   print $ extractClassName dec
   print $ join (extractAtomsTopLevel <$> parseDecs fundef1)
   let Right nms = join (extractAtomsTopLevel <$> parseDecs fundef1)


   print $ join <$> (sequence [(Right ["a","b"] :: Either String [String]),Right ["c","d"]])


transformation :: QuasiQuoter
transformation = QuasiQuoter { quoteDec = parseTransformation }

hardError :: Either String a -> a
hardError (Left err) = error err
hardError (Right a) = a

parseTransformation :: String -> Q [Dec]
parseTransformation dsl = do 
  let hsyn = parseDecs dsl
  case hsyn of 
    Left err -> error err
    Right pa -> do
      let atoms = hardError $ extractAtomsTopLevel pa
          classname = hardError $ extractClassName $ head pa
          funname = hardError $ extractFunName $ head pa
      fullats <- fullNameAtoms atoms
      let context = []
          tyvar = mkName "f"
          threadnm = mkName "s"
          fundeps = []
          sigdecs = makeSig funname threadnm tyvar
          chname = hardError $ extractChangedName $ head pa
          patbods = hardError $ extractPatBodyPairs $ head pa
          pt = mkPatternTree $ fst <$> patbods
      fundecs <- buildTransformer funname chname tyvar patbods 
      pure [ClassD (mkCtx fullats tyvar) classname [PlainTV tyvar] fundeps sigdecs
           ,InstanceD Nothing (mkCtx fullats tyvar) (AppT (ConT classname) (VarT tyvar)) fundecs
           ]


data TopCtx = TopCtx {
    changedName :: Name,
    topTag :: Name,
    topRes :: Name,
    tyVar :: Name
}

buildTransformer :: Name -> Name -> Name -> [(Pat,Body)] -> Q [Dec]
buildTransformer funname chname tyvar patbods = do
   (Tag tag, Res res, varbind) <- topVariantBind (fst <$> patbods)
   body   <- pure $ (VarE (mkName "undefined")) --transformerBody (TopCtx chname toptag topres tyvar) split 
   pure [FunD funname [Clause [VarP chname, varbind] (NormalB body) []]]

transformerBody :: TopCtx -> (MatchedOut, [(Pat, Body)]) -> Q Exp 
transformerBody ctx (mo, nomo) = do
    let lastag = patTag mo
        lastres = patRes mo
        tyvar = tyVar ctx 
    matchB <- matchBranch ctx mo
    fallThroughB <- fallThroughBody ctx nomo
    pure (CaseE (AppE (AppE (VarE (mkName "testEquality")) (VarE lastag)) 
                         (AppTypeE (VarE (mkName "fromSides")) (AppT (AppT (ConT (mkName "Locate"))
                         (ConT (patName mo))) (VarT tyvar)))) 
                     [Match (ConP (mkName "Just") [ConP (mkName "Refl") []]) (NormalB (CaseE (VarE lastres) matchB)) [] 

                     ,Match WildP (NormalB fallThroughB) [] 
                     ]
                   )


transformerBody' :: TopCtx -> MatchedOut -> [Match] -> Exp -> Q Exp 
transformerBody' ctx mo matchB fallThroughB = do
    let lastag = patTag mo
        lastres = patRes mo
        tyvar = tyVar ctx 
    pure (CaseE (AppE (AppE (VarE (mkName "testEquality")) (VarE lastag)) 
                         (AppTypeE (VarE (mkName "fromSides")) (AppT (AppT (ConT (mkName "Locate"))
                         (ConT (patName mo))) (VarT tyvar)))) 
                     [Match (ConP (mkName "Just") [ConP (mkName "Refl") []]) (NormalB (CaseE (VarE lastres) matchB)) [] 

                     ,Match WildP (NormalB fallThroughB) [] 
                     ]
                   )

-- And (Not a) (Not b) = ...
-- And x e
--
--

--constructorHoleFill :: Either (Name, [Pat]) Name -> Q (Either (Name, Name, Pat) Pat))
--constructorHoleFill (Right v) = pure $ VarP v
--constructorHoleFill (Left (con, _)) = do 
--   tagin <- newName
--   resin <- newName
--   pure $ ConP (mkName "Pure") [ConP (mkName "Molecule") [ConP (mkName "VariantF") [VarP tagin,VarP resin]]]

-- c@(VariantF tag res)
-- ((A ...), aBod)   | case testEquality tag (fromSides @(Locate A t)) of
-- ((A ...), aBod')  |   Just Refl -> case res of
-- ((A ...), aBod'') |                  A ... ->
-- ((B ...), bBod)   |   _ -> case testEquality tag (fromSides @(Locate B t)) of
--                   |          Just Refl -> case res of
--                   |                         B ... ->
-- ((c    ), cBod)   |          _ -> 
--
--                               VariantBind
--splitPatterns' :: [(Pat,Body)] -> ? 
--splitPatterns' =
--  let fmap (\(pat,bod) -> (patternHead pat, bod)) patbods

hasBoundName :: [Pat] -> Maybe Name
hasBoundName pats = 
  let ptypes = patternType <$> pats 
      boundn = join ((\case 
                         Bind nm -> [nm]
                         _ -> []) <$> ptypes)
  in case nub (sort boundn) of
       [] -> Nothing
       [b] -> Just b
       err -> error $ "Conflicting names bound for same pattern: " ++ show err

topVariantBind :: [Pat] -> Q (Tag, Res, Pat)
topVariantBind pats = do
  tag <- newName "tag"
  res <- newName "res"
  case hasBoundName pats of
    Just nm ->
      pure $ (Tag tag, Res res, AsP nm (ConP (mkName "VariantF") [VarP tag, VarP res]))
    Nothing ->    
      pure $ (Tag tag, Res res, (ConP (mkName "VariantF") [VarP tag, VarP res]))

variantBind :: [Pat] -> Q (Tag, Res, Pat)
variantBind pats = do
  (tag, res, vpat) <- topVariantBind pats
  pure (tag, res, (ConP (mkName "Pure")
                  [ConP (mkName "Molecule") 
                  [vpat]]))

partSingleDim :: Tag -> Res -> [(Pat,Body)] -> [PatternPart]
partSingleDim tag res patbods =
  let typed = (\(p,b) -> (patternType p, b)) <$> patbods 
    in partSingleDimTyped tag res typed
  
partSingleDimTyped :: Tag -> Res -> [(PatternType, Body)] -> [PatternPart]
partSingleDimTyped _ _ [] = []
partSingleDimTyped _ _ ((Blank, b):rest) =
  if length rest > 0
    then error $ "Redundant patterns due to WildP capture." ++ show rest
    else [NoProof b] 
partSingleDimTyped _ _ ((Bind nm, b):rest) =
  if length rest > 0
    then error $ "Redundant patterns due to " ++ show nm ++ " capture." ++ show rest
    else [NoProof b] 
partSingleDimTyped tag res pats@((Constructed nm _, _):_) =
  let topPats = filter (\case
                           (Constructed ni _, _) -> ni == nm
                           _ -> False
                       ) pats
      restPats = filter (\case
                            (Constructed ni _, _) -> ni /= nm
                            _ -> True
                        ) pats
      proofo = ProofOf tag res nm $ map (\case
                                           (Constructed _ pats, body) -> (pats,body)
                                           _ -> error "impossible"
                                       ) topPats
    in proofo:(partSingleDimTyped tag res restPats) 

newtype Bin = Bin Name deriving (Eq, Show)
newtype Tag = Tag Name   deriving (Eq, Show) 
newtype Res = Res Name   deriving (Eq, Show) 
newtype Cons = Cons Name deriving (Eq, Show) 


data PatternPart = NoProof Body 
                 | ProofOf Tag Res Cons [([Pat],Body)]

-- (And (Not a) (Or _ (Not b)))
-- (And c d
-- (Not f
-- (Or (And l r) (Not x)
-- ProofNode And [ProofNode Not [Bound a] , ProofNode Or [Wildo , ProofNode Not [Bound b] ] ]
-- ProofNode And [Bound c                 , Bound d]
-- ProofNode Not [Bound f]
-- ProofNode Or  [ProofNode And [Bound l, Bound r], ProofNode Not [Bound x]]
data PatternTree = Bound [BC] | ProofNode [BC] [PatternTree] deriving (Eq, Show) 

data BC = B Name | C Name deriving (Eq, Show)

mkPatternTree :: [Pat] -> PatternTree
mkPatternTree [] = error "no patterns!"
mkPatternTree pats =
   let (h:t) = patternTree <$> pats
     in foldr zipPatternTree h t

patternTree :: Pat -> PatternTree
patternTree WildP = Bound [] 
patternTree (VarP v) = Bound [B v] 
patternTree (ConP con pats) = ProofNode [C con] (patternTree <$> pats) 
patternTree (ParensP p) = patternTree p
patternTree  p = error $ "Unsupported pattern construction " ++ show p

zipPatternTree :: PatternTree -> PatternTree -> PatternTree
zipPatternTree (Bound v) (Bound q) = Bound (filterBC ( v ++ q )) 
zipPatternTree (ProofNode cl tl) (ProofNode cr tr) = ProofNode (filterBC (cl ++ cr)) (zipWith zipPatternTree tl tr)
zipPatternTree (Bound l) (ProofNode c t) = ProofNode (filterBC (l ++ c)) t
zipPatternTree (ProofNode l t) (Bound r) = ProofNode (filterBC (l ++ r)) t

filterBC :: [BC] -> [BC]
filterBC [] = []
filterBC (h:t) = h:(filter (/= h) t) 

buildTransformer' :: Name -> Name -> Name -> [(Pat,Body)] -> Q [Dec]
buildTransformer' funname chname tyvar patbods = do
   (tag, res, pat) <- topVariantBind (fst <$> patbods)
   body <- undefined
   pure [FunD funname [Clause [VarP chname, pat] (NormalB body) []]]


data PatternType = Blank | Bind Name | Constructed Cons [Pat] deriving Show


patternType :: Pat -> PatternType 
patternType WildP = Blank
patternType (VarP v) = Bind v
patternType (ConP con pats) = Constructed (Cons con) pats
patternType (ParensP pat) = patternType pat
patternType p = error $ "Unsupported pattern construction " ++ show p


data MatchedOut = MatchedOut {
    patName :: Name,
    patTag :: Name,
    patRes :: Name,
    inMatch :: [([Pat],Body)] 
}

splitPatterns :: [(Pat,Body)] -> Q ( MatchedOut , [(Pat,Body)])
splitPatterns [] = error "Somehow there are no patterns? I expected patterns..."
splitPatterns patbods  = undefined
--  let headed = fmap (\(pat,bod) -> (patternHead pat, bod)) patbods
--      firstcon = head headed


matchBranch :: TopCtx -> MatchedOut -> Q [Match]
matchBranch ctx mo = undefined

fallThroughBody :: TopCtx -> [(Pat,Body)] -> Q Exp 
fallThroughBody ctx [] =
    pure $ (AppE (VarE (mkName "pure"))
                         (AppE (ConE (mkName "Pure"))
                         (AppE (ConE (mkName "Molecule"))
                         (AppE (AppE (ConE (mkName "VariantF")) (VarE (topTag ctx))) (VarE (topRes ctx))))))
fallThroughBody ctx patbods = do
   split@(match, _) <- splitPatterns patbods 
   let toptag = topTag ctx 
       topres = topRes ctx
   transformerBody ctx split 


--(NormalB (CaseE (VarE lastres) fallThroughB))

--[FunD Atoms.Chemistry.Utils.TH.doubleNegation [Clause [VarP changed_5,ConP Type.Set.VariantF.VariantF [VarP tag_6,VarP res_7]] 
-- (NormalB (CaseE (AppE (AppE (VarE Data.Type.Equality.testEquality) (VarE tag_6)) (AppTypeE (VarE Type.Set.Variant.fromSides) (AppT (AppT (ConT Type.Set.Locate) (ConT Atoms.Elements.PropCalc.Not.Not)) (VarT t_4))))
--    [Match (ConP GHC.Maybe.Just [ConP Data.Type.Equality.Refl []]) (NormalB (CaseE (VarE res_7) 
--
--        [Match (ConP Atoms.Elements.PropCalc.Not.Not [ConP Hyper.Type.Pure.Pure [ConP Atoms.Molecule.AST.Molecule [ConP Type.Set.VariantF.VariantF [VarP tagi_8,VarP resi_9]]]]) (NormalB (CaseE (AppE (AppE (VarE Data.Type.Equality.testEquality) (VarE tagi_8)) (AppTypeE (VarE Type.Set.Variant.fromSides) (AppT (AppT (ConT Type.Set.Locate) (ConT Atoms.Elements.PropCalc.Not.Not)) (VarT t_4))))
--            [Match (ConP GHC.Maybe.Just [ConP Data.Type.Equality.Refl []]) (NormalB (CaseE (VarE resi_9) 
--               [Match (ConP Atoms.Elements.PropCalc.Not.Not [VarP a_10]) (NormalB (DoE [NoBindS (AppE (AppE (VarE GHC.STRef.writeSTRef) (VarE changed_5)) (ConE GHC.Types.True)),NoBindS (AppE (VarE GHC.Base.pure) (VarE a_10))])) []])) [],
--             Match (ConP GHC.Maybe.Nothing []) (NormalB (InfixE (Just (VarE GHC.Base.pure)) (VarE GHC.Base.$) (Just (InfixE (Just (ConE Hyper.Type.Pure.Pure)) (VarE GHC.Base.$) (Just (AppE (ConE Atoms.Molecule.AST.Molecule) (AppE (AppE (ConE Type.Set.VariantF.VariantF) (VarE tag_6)) (VarE res_7)))))))) []])) []])) [],
--
--     Match WildP (NormalB (AppE (VarE GHC.Base.pure) (AppE (ConE Hyper.Type.Pure.Pure) (AppE (ConE Atoms.Molecule.AST.Molecule) (AppE (AppE (ConE Type.Set.VariantF.VariantF) (VarE tag_6)) (VarE res_7)))))) []])) []]]

makeHasF :: Name -> Name -> Type 
makeHasF atom tyvar = AppT (AppT (ConT (mkName "Type.Set.VariantF.HasF")) (ConT atom)) (VarT tyvar)

makeForAllIn :: Name -> Name -> Type
makeForAllIn fclass tyvar = AppT (AppT (ConT (mkName "Type.Set.Variant.ForAllIn")) (ConT fclass)) (VarT tyvar)

makeFromSidesLocate :: Name -> Name -> Type
makeFromSidesLocate atom tyvar =
    (AppT (ConT (mkName "Type.Set.Variant.FromSides")) 
    (AppT (AppT (ConT (mkName "Type.Set.Locate")) (ConT atom)) (VarT tyvar)))

makeFollowLocate :: Name -> Name -> Type
makeFollowLocate atom tyvar =
    (AppT (AppT EqualityT (AppT (AppT (ConT (mkName "Type.Set.Follow"))
    (AppT (AppT (ConT (mkName "Type.Set.Locate")) (ConT atom)) (VarT tyvar))) (VarT tyvar))) (ConT atom))

makeSig :: Name -> Name -> Name -> [Dec]
makeSig signame threadname tyvar =
    [SigD signame (AppT (AppT ArrowT (AppT (AppT (ConT (mkName "STRef")) (VarT threadname)) (ConT (mkName "Bool"))))
      (AppT (AppT ArrowT (AppT (AppT (ConT (mkName "Type.Set.VariantF.VariantF")) (VarT tyvar))
      (AppT (AppT (ConT (mkName "#")) (ConT (mkName "Hyper.Type.Pure.Pure")))
            (AppT (ConT (mkName "Atoms.Molecule.AST.Molecule"))
            (AppT (ConT (mkName "Type.Set.VariantF.VariantF")) (VarT tyvar))))))
                  (AppT (AppT (ConT (mkName "ST")) (VarT threadname))
                  (AppT (AppT (ConT (mkName "#")) (ConT (mkName "Hyper.Type.Pure.Pure")))
                  (AppT (ConT (mkName "Atoms.Molecule.AST.Molecule"))
                  (AppT (ConT (mkName "Type.Set.VariantF.VariantF")) (VarT tyvar)))))))]

mkCtx :: [Name] -> Name -> [Type]
mkCtx atoms tyvar =
  ((flip makeHasF) tyvar <$> atoms) ++
  ((flip makeFromSidesLocate) tyvar <$> atoms) ++
  ((flip makeFollowLocate) tyvar <$> atoms) ++
  [ makeForAllIn (mkName "Functor") tyvar
  , makeForAllIn (mkName "Foldable") tyvar
  , makeForAllIn (mkName "Traversable") tyvar
  ]

-- | the class name will just be the function name with the first char capitalised 
extractClassName :: Dec -> Either String Name
extractClassName (FunD nm _ ) = 
    let f:rest = show nm 
      in Right $ mkName ((toUpper f):rest)
extractClassName _ = Left "Expecting top level function definition."

extractChangedName :: Dec -> Either String Name
extractChangedName (FunD _ clauses) =
  case join <$> (sequence (extractChangedNameC <$> clauses)) of
    Left err -> Left err
    Right nms ->
      case nub (sort nms) of
        [c] -> Right c
        _ -> Left "Expected all STRef Bool variable bindings to take the same name"
extractChangedName _ = Left "Expected a function declaration"

extractPatBodyPairs :: Dec -> Either String [(Pat,Body)]
extractPatBodyPairs (FunD _ clauses) = join <$> (sequence (extractPatBodyPair <$> clauses))
extractPatBodyPairs _ = Left "Expected a top level function definition."

extractPatBodyPair :: Clause -> Either String [(Pat,Body)]
extractPatBodyPair (Clause [_,pat] body []) = Right [(pat,body)]
extractPatBodyPair _ = Left "Expecting clause of form (Var STRef Bool) (Pat Atom) = body."

extractChangedNameC :: Clause -> Either String [Name]
extractChangedNameC (Clause [VarP changed,_] _ _) = Right [changed]
extractChangedNameC _ = Left "Expecting an STRef Bool variable binding pattern and an Atom pattern expresion"  

extractFunName :: Dec -> Either String Name
extractFunName (FunD nm _ ) = Right nm
extractFunName _ = Left "Expecting top level function definition."

-- | Extracts all top level constructors.
-- TH function will take a blacklist of constructor names to allow constructors that are not Atoms to appear e.g. True
extractAtomsTopLevel :: [Dec] -> Either String [Name]
extractAtomsTopLevel [fun] = (nub . sort) <$> extractAtomsFunD fun
extractAtomsTopLevel _ = Left "Expecting a single top level function definition."

extractAtomsFunD :: Dec -> Either String [Name]
extractAtomsFunD (FunD _ clauses) = join <$> (sequence (extractAtomsClause <$> clauses)) 
extractAtomsFunD _ = Left "Expecting top level function definition."

extractAtomsClause :: Clause -> Either String [Name]
extractAtomsClause (Clause (changed:[pat]) body []) = join <$> (sequence [extractAtomsPat pat, extractAtomsBody body]) 
extractAtomsClause (Clause [] _ [])        = Left "Expecting function to pattern match on an Atom. There is no pattern."
extractAtomsClause (Clause (changed:(pat:_)) _ [])   = Left "Expecting a single Atom pattern in function."
extractAtomsClause (Clause _ _ _)         = Left "This template does not support where declarations."

extractAtomsPat :: Pat -> Either String [Name]
extractAtomsPat (ConP nm inside) = (nm:) <$> (join <$> sequence (extractAtomsPat <$> inside)) 
extractAtomsPat (ParensP pat) = extractAtomsPat pat
extractAtomsPat (VarP _) = Right []
extractAtomsPat WildP = Right []
extractAtomsPat pat = Left $ "Unsupported pattern element: " ++ show pat

extractAtomsBody :: Body -> Either String [Name]
extractAtomsBody (NormalB exp) = extractAtomsExp exp 
extractAtomsBody (GuardedB guardedExps) = join <$> (sequence (extractAtomsExp <$> (snd <$> guardedExps))) 

extractAtomsExp :: Exp -> Either String [Name]
extractAtomsExp (AppE expl expr) = join <$> (sequence [extractAtomsExp expl, extractAtomsExp expr])
extractAtomsExp (DoE exprs) = join <$> (sequence (extractAtomsStmt <$> exprs))  
extractAtomsExp (ConE nm) = Right [nm]
extractAtomsExp (VarE _) = Right []
extractAtomsExp exp = Left $ "Unsupported expression: " ++ show exp

extractAtomsStmt :: Stmt -> Either String [Name]
extractAtomsStmt (NoBindS expr) = extractAtomsExp expr 
extractAtomsStmt stmt = Left $ "Unsupported statement: " ++ show stmt

fullNameAtoms :: [Name] -> Q [Name]
fullNameAtoms [] = pure []
fullNameAtoms (a:as) = do
  lun <- lookupTypeName $ show a
  ren <- fullNameAtoms as
  case lun of
    Nothing -> pure ren 
    Just lo -> do
      if isPrefixOf "Atoms.Elements" (show lo)
        then pure (lo:ren)
        else pure ren
 
printClassDec :: IO ()
printClassDec = do
   e <- runQ [d| class ( HasF Not t
                       , ForAllIn Functor t
                       , ForAllIn Foldable t
                       , ForAllIn Traversable t
                       , Follow (Locate Not t) t ~ Not 
                       , FromSides (Locate Not t)
                       ) => DoubleNegation t where
                     doubleNegation ::  STRef s Bool
                                    -> VariantF t (Pure # Molecule (VariantF t))
                                    -> ST s (Pure # Molecule (VariantF t))

            |]
   print e

printInstanceDec :: IO ()
printInstanceDec = do
   e <- runQ [d| instance ( HasF Not t
                          , ForAllIn Functor t
                          , ForAllIn Foldable t
                          , ForAllIn Traversable t
                          , Follow (Locate Not t) t ~ Not 
                          , FromSides (Locate Not t)
                          ) => DoubleNegation t where
                     doubleNegation changed (VariantF tag res) =
                         case testEquality tag (fromSides @(Locate Not t)) of
                             Just Refl ->
                                 case res of
                                     Not a@(Pure (Molecule (VariantF tagi resi))) ->
                                         case testEquality tagi (fromSides @(Locate Not t)) of
                                             Just Refl ->
                                                case resi of
                                                   Not a -> do
                                                      writeSTRef changed True
                                                      pure a 
                                             Nothing -> pure $ Pure $ Molecule (VariantF tag res) 
                             _ -> pure (Pure (Molecule (VariantF tag res)))
             |]
   print e

