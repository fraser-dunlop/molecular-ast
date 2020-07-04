{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
module Atoms.Chemistry.Utils.TH where
import Atoms.Chemistry.Utils.TH.CaseTree
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

import Data.Generics.Uniplate.Data

import Control.Monad (join)
import Data.List (sort,nub)
import Data.Char (toUpper)
import Data.List (isPrefixOf,transpose)
import Debug.Trace 

transformation :: QuasiQuoter
transformation = QuasiQuoter { 
    quoteExp  = error "transformation is not an Exp quoter",
    quotePat  = error "transformation is not a Pat quoter",
    quoteType = error "transformation is not a Type quoter",
    quoteDec  = parseTransformation
  }

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
      tyvar <- newName "f"
      threadnm <- newName "s"
      chname <- newName $ hardError $ extractChangedName $ head pa
      let context = []
          fundeps = []
          sigdecs = makeSig funname threadnm tyvar          
          patbods = hardError $ extractPatBodyPairs $ head pa
      fundecs <- buildTransformer funname chname tyvar patbods 
      pure [ClassD (mkCtx fullats tyvar) classname [PlainTV tyvar] fundeps sigdecs
           ,InstanceD Nothing (mkCtx fullats tyvar) (AppT (ConT classname) (VarT tyvar)) fundecs
           ]



buildTransformer :: Name -> Name -> Name -> [(Pat,Body)] -> Q [Dec]
buildTransformer funname chname tyvar patbods = do
  ct <- buildCaseTree patbods
  writeCaseTree funname chname tyvar ct

writeCaseTree :: Name -> Name -> Name -> CaseTree [Body] -> Q [Dec]
writeCaseTree funname chname tyvar ct = do 
  (varbind, body) <- templateCaseTree tyvar ct 
  pure [FunD funname [Clause [VarP chname , varbind] body []]]


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

extractChangedName :: Dec -> Either String String 
extractChangedName (FunD _ clauses) =
  case join <$> (sequence (extractChangedNameC <$> clauses)) of
    Left err -> Left err
    Right nms ->
      case nub (sort nms) of
        [c] -> Right $ show c
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
extractAtomsClause (Clause (changed:[pat]) body []) =
  Right $ extractAtomsPat pat ++ extractAtomsBody body
extractAtomsClause (Clause [] _ [])        = Left "Expecting function to pattern match on an Atom. There is no pattern."
extractAtomsClause (Clause (changed:(pat:_)) _ [])   = Left "Expecting a single Atom pattern in function."
extractAtomsClause (Clause _ _ _)         = Left "This template does not support where declarations."

extractAtomsPat :: Pat -> [Name]
extractAtomsPat p = [ nm | ConP nm _ <- universe p] ++ [ nm | UInfixP _ nm _ <- universe p]


extractAtomsBody :: Body -> [Name]
extractAtomsBody (NormalB exp) = extractAtomsExp exp 
extractAtomsBody (GuardedB guardedExps) = 
   join (extractAtomsGuard <$> (fst <$> guardedExps)) 
   ++ join (extractAtomsExp <$> (snd <$> guardedExps)) 

extractAtomsGuard :: Guard -> [Name]
extractAtomsGuard (NormalG e) = [i | ConE i <- universe e]
extractAtomsGuard (PatG stmts) = join (extractAtomsStmt <$> stmts)


extractAtomsExp :: Exp -> [Name]
extractAtomsExp e = [i | ConE i <- universe e]

extractAtomsStmt :: Stmt -> [Name]
extractAtomsStmt (NoBindS expr) = extractAtomsExp expr 
extractAtomsStmt (LetS decs) = join (extractAtomsDec <$> decs)
extractAtomsStmt (BindS p e) = extractAtomsPat p ++ extractAtomsExp e
extractAtomsStmt (RecS stmts) = join (extractAtomsStmt <$> stmts)
extractAtomsStmt _ = error "unsupported statement"

extractAtomsDec :: Dec -> [Name]
extractAtomsDec (ValD p b decs) =
   extractAtomsPat p ++ extractAtomsBody b ++ (join (extractAtomsDec <$> decs))  

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
 
