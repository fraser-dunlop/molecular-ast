{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Chemistry.Transformations.DoubleNegation where
import Atoms.Elements.Not
import Atoms.Molecule.AST
import Data.Type.Equality
import Hyper
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF

class DoubleNegation t where
    doubleNegation :: VariantF t (Pure # Molecule (VariantF t))
                   -> Pure # Molecule (VariantF t)

instance ( HasF Not t
         , ForAllIn Functor t
         , Follow (Locate Not t) t ~ Not 
         , FromSides (Locate Not t)
         ) => DoubleNegation t where
    doubleNegation (VariantF (tag :: SSide ss) res) =
        case testEquality tag (fromSides @(Locate Not t)) of
            Just Refl ->
                case res of
                    Not (Pure (Molecule (VariantF (tagi :: SSide ssi) resi))) ->
                        case testEquality tagi (fromSides @(Locate Not t)) of
                            Just Refl ->
                               case resi of
                                  Not a -> a 
                            Nothing -> Pure $ Molecule (VariantF tag res) 
            Nothing -> Pure $ Molecule (VariantF tag res)

