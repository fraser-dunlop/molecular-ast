{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Chemistry.Transformations.DeMorgan where
import Atoms.Elements.And
import Atoms.Elements.Not
import Atoms.Elements.Or
import Atoms.Molecule.AST
import Data.Type.Equality
import Hyper
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF

class DeMorgan t where
    deMorganNegationOfDisjunction :: VariantF t (Pure # Molecule (VariantF t))
                                  -> Pure # Molecule (VariantF t)
    deMorganNegationOfConjunction :: VariantF t (Pure # Molecule (VariantF t))
                                  -> Pure # Molecule (VariantF t)

instance ( HasF And t
         , HasF Not t
         , HasF Or t
         , ForAllIn Functor t
         , Follow (Locate And t) t ~ And 
         , FromSides (Locate And t)
         , Follow (Locate Not t) t ~ Not 
         , FromSides (Locate Not t)
         , Follow (Locate Or t) t ~ Or 
         , FromSides (Locate Or t)
         ) => DeMorgan t where
    deMorganNegationOfDisjunction (VariantF (tag :: SSide ss) res) =
        case testEquality tag (fromSides @(Locate Not t)) of
            Just Refl ->
                case res of
                    Not (Pure (Molecule (VariantF (tagi :: SSide ssi) resi))) ->
                        case testEquality tagi (fromSides @(Locate Or t)) of
                            Just Refl ->
                               case resi of
                                  Or a b -> (iNot a) `iAnd` (iNot b)
                            Nothing -> Pure $ Molecule (VariantF tag res) 
            Nothing -> Pure $ Molecule (VariantF tag res)
    deMorganNegationOfConjunction (VariantF (tag :: SSide ss) res) =
        case testEquality tag (fromSides @(Locate Not t)) of
            Just Refl ->
                case res of
                    Not (Pure (Molecule (VariantF (tagi :: SSide ssi) resi))) ->
                        case testEquality tagi (fromSides @(Locate And t)) of
                            Just Refl ->
                               case resi of
                                  And a b -> (iNot a) `iOr` (iNot b)
                            Nothing -> Pure $ Molecule (VariantF tag res) 
            Nothing -> Pure $ Molecule (VariantF tag res)
