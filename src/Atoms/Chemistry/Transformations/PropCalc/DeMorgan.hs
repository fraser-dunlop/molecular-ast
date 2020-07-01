{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Chemistry.Transformations.PropCalc.DeMorgan where
import Atoms.Elements.PropCalc.And
import Atoms.Elements.PropCalc.Not
import Atoms.Elements.PropCalc.Or
import Atoms.Molecule.AST
import Data.Type.Equality
import Hyper
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF
import Data.STRef
import Control.Monad.ST

class ( HasF And t
      , HasF Not t
      , HasF Or t
      , ForAllIn Functor t
      , ForAllIn Foldable t
      , ForAllIn Traversable t
      , Follow (Locate And t) t ~ And 
      , FromSides (Locate And t)
      , Follow (Locate Not t) t ~ Not 
      , FromSides (Locate Not t)
      , Follow (Locate Or t) t ~ Or 
      , FromSides (Locate Or t)
      ) => DeMorgan t where
    deMorganNegationOfDisjunction :: STRef s Bool
                                  -> VariantF t (Pure # Molecule (VariantF t))
                                  -> ST s (Pure # Molecule (VariantF t))
    deMorganNegationOfConjunction :: STRef s Bool
                                  -> VariantF t (Pure # Molecule (VariantF t))
                                  -> ST s (Pure # Molecule (VariantF t))

instance ( HasF And t
         , HasF Not t
         , HasF Or t
         , ForAllIn Functor t
         , ForAllIn Foldable t
         , ForAllIn Traversable t
         , Follow (Locate And t) t ~ And 
         , FromSides (Locate And t)
         , Follow (Locate Not t) t ~ Not 
         , FromSides (Locate Not t)
         , Follow (Locate Or t) t ~ Or 
         , FromSides (Locate Or t)
         ) => DeMorgan t where
    deMorganNegationOfDisjunction changed node@(VariantF (tag :: SSide ss) res) =
        case testEquality tag (fromSides @(Locate Not t)) of
            Just Refl ->
                case res of
                    Not (Pure (Molecule (VariantF (tagi :: SSide ssi) resi))) ->
                        case testEquality tagi (fromSides @(Locate Or t)) of
                            Just Refl ->
                               case resi of
                                  Or a b -> do
                                     writeSTRef changed True
                                     pure $ (iNot a) `iAnd` (iNot b)
                            Nothing -> pureVNode node 
            Nothing -> pureVNode node
    deMorganNegationOfConjunction changed node@(VariantF (tag :: SSide ss) res) =
        case testEquality tag (fromSides @(Locate Not t)) of
            Just Refl ->
                case res of
                    Not (Pure (Molecule (VariantF (tagi :: SSide ssi) resi))) ->
                        case testEquality tagi (fromSides @(Locate And t)) of
                            Just Refl ->
                               case resi of
                                  And a b -> do
                                      writeSTRef changed True
                                      pure $ (iNot a) `iOr` (iNot b)
                            Nothing -> pureVNode node 
            Nothing -> pureVNode node 
