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
                                     Not (Pure (Molecule (VariantF tagi resi))) ->
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
   f <- runQ $ [d| func (Not (Not s)) = s
                   func (Not x) = x
                 |]
   print f



-- doubleNegation (Not (Not x)) = x
--notnot = [Transformation "doubleNegation" (Pattern "Not" [Pattern "Not" [Binding "a"]]) 
--         ,Transformation "doubleNegation" (]

data Constructor = Constructor String
data Pattern = Pattern Constructor [Pattern] | Binding String
-- transformationName (Pattern (Pattern ...) (Pattern ...) ...) = Pattern 
data Transformation = Transformation String Pattern Pattern

newtype SSidesRef = SSidesRef Name 
newtype VariantRef = VariantRef Name 
newtype DataTypeName = DataTypeName Name
data Context = Context {
    hyperTypesPure :: Name --Hyper.Types.Base.Pure
  , ghcBasePure :: Name    --GHC.Base.pure
  , atomsASTMolecule :: Name -- Atoms.Molecule.AST.Molecule
  , typeSetVariantF :: Name  -- Type.Set.VariantF.VariantF
  , atomSet :: Name -- t
  , dataTypeTestEquality :: Name -- Data.Type.Equality.testEquality
  , typeSetVariantFromSides :: Name -- Type.Set.Variant.fromSides
  , typeSetLocate :: Name -- Type.Set.Locate
}

-- pure (Pure (Molecule (VariantF tag res)))
rawReturn :: Context -> SSidesRef -> VariantRef -> Body
rawReturn ctx (SSidesRef tag) (VariantRef res) =
     (NormalB (AppE (VarE (ghcBasePure ctx))
              (AppE (ConE (hyperTypesPure ctx))
              (AppE (ConE (atomsASTMolecule ctx)) 
              (AppE (AppE (ConE (typeSetVariantF ctx)) (VarE tag)) (VarE res))))))

-- _ -> body
blankPatternRet :: Body -> Match
blankPatternRet body = Match WildP body [] 

-- testEquality tag (fromSides @(Locate DataTypeName t)) 
proveMatch :: Context -> SSidesRef -> DataTypeName -> Exp
proveMatch ctx (SSidesRef tag) (DataTypeName dataTypeName) = 
     (AppE (AppE (VarE (dataTypeTestEquality ctx))
                 (VarE tag)) (AppTypeE (VarE (typeSetVariantFromSides ctx))
                                       (AppT (AppT (ConT (typeSetLocate ctx)) 
                                                   (ConT dataTypeName)) (VarT (atomSet ctx)))))



-- InstanceD
--   Nothing 
--   [AppT (AppT (ConT HasF) (ConT Not)) (VarT t_0)
--   ,AppT (AppT EqualityT (AppT (AppT (ConT Follow) (AppT (AppT (ConT Locate) (ConT Not)) (VarT t_0))) (VarT t_0))) (ConT Not)
--   ,AppT (ConT FromSides) (AppT (AppT (ConT Locate) (ConT Not)) (VarT t_0))
--
--   ,AppT (AppT (ConT ForAllIn) (ConT Functor)) (VarT t_0)
--   ,AppT (AppT (ConT ForAllIn) (ConT Foldable)) (VarT t_0)
--   ,AppT (AppT (ConT ForAllIn) (ConT Traversable)) (VarT t_0)
--   ] 
--   (AppT (ConT DoubleNegation) (VarT t_0))
--   [FunD doubleNegation 
--     [Clause [VarP changed, ConP VariantF [VarP tag, VarP res]]
--      (NormalB
--       (CaseE (AppE (AppE (VarE testEquality) (VarE tag)) (AppTypeE (VarE fromSides) (AppT (AppT (ConT Locate) (ConT Not)) (VarT t))))
--         [Match (ConP GHC.Maybe.Just [ConP Data.Type.Equality.Refl []]) 
--                (NormalB (CaseE (VarE res_3) [Match (ConP Atoms.Elements.PropCalc.Not.Not [ConP Hyper.Type.Pure.Pure [ConP Atoms.Molecule.AST.Molecule [ConP Type.Set.VariantF.VariantF [VarP tagi_4,VarP resi_5]]]]) (NormalB (CaseE (AppE (AppE (VarE Data.Type.Equality.testEquality) (VarE tagi_4)) (AppTypeE (VarE Type.Set.Variant.fromSides) (AppT (AppT (ConT Type.Set.Locate) (ConT Atoms.Elements.PropCalc.Not.Not)) (VarT t_0)))) [Match (ConP GHC.Maybe.Just [ConP Data.Type.Equality.Refl []]) (NormalB (CaseE (VarE resi_5) [Match (ConP Atoms.Elements.PropCalc.Not.Not [VarP a_6]) (NormalB (DoE [NoBindS (AppE (AppE (VarE GHC.STRef.writeSTRef) (VarE changed_1)) (ConE GHC.Types.True)),NoBindS (AppE (VarE GHC.Base.pure) (VarE a_6))])) []])) [],Match (ConP GHC.Maybe.Nothing []) (NormalB (InfixE (Just (VarE GHC.Base.pure)) (VarE GHC.Base.$) (Just (InfixE (Just (ConE Hyper.Type.Pure.Pure)) (VarE GHC.Base.$) (Just (AppE (ConE Atoms.Molecule.AST.Molecule) (AppE (AppE (ConE Type.Set.VariantF.VariantF) (VarE tag_2)) (VarE res_3)))))))) []])) []])) []
--          ,Match (ConP Nothing []) (NormalB (InfixE (Just (VarE pure)) (VarE $) (Just (InfixE (Just (ConE Pure)) (VarE $) (Just (AppE (ConE Molecule) (AppE (AppE (ConE VariantF) (VarE tag)) (VarE res)))))))) []
--          ])) []
--     ]
--   ]
