{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Chemistry.Transformations.PropCalc.NegateLitBool where
import Atoms.Elements.PropCalc.LitBool
import Atoms.Elements.PropCalc.Not
import Atoms.Molecule.AST
import Data.Type.Equality
import Hyper
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF
import Data.STRef
import Control.Monad.ST

class ( HasF LitBool t
      , HasF Not t
      , ForAllIn Functor t
      , ForAllIn Foldable t
      , ForAllIn Traversable t
      , Follow (Locate LitBool t) t ~ LitBool 
      , FromSides (Locate LitBool t)
      , Follow (Locate Not t) t ~ Not 
      , FromSides (Locate Not t)
      ) => NegateLitBool t where
    negateLitBool ::  STRef s Bool
                   -> VariantF t (Pure # Molecule (VariantF t))
                   -> ST s (Pure # Molecule (VariantF t))

instance ( HasF Not t
         , HasF LitBool t
         , ForAllIn Functor t
         , ForAllIn Foldable t
         , ForAllIn Traversable t
         , Follow (Locate LitBool t) t ~ LitBool 
         , FromSides (Locate LitBool t)
         , Follow (Locate Not t) t ~ Not 
         , FromSides (Locate Not t)
         ) => NegateLitBool t where
    negateLitBool changed (VariantF (tag :: SSide ss) res) =
        case testEquality tag (fromSides @(Locate Not t)) of
            Just Refl ->
                case res of
                    Not (Pure (Molecule (VariantF (tagi :: SSide ssi) resi))) ->
                        case testEquality tagi (fromSides @(Locate LitBool t)) of
                            Just Refl ->
                               case resi of
                                  LitBool a -> do
                                     writeSTRef changed True
                                     pure (iLitBool (not a)) 
                            Nothing -> pure $ Pure $ Molecule (VariantF tag res) 
            Nothing -> pure $ Pure $ Molecule (VariantF tag res)

