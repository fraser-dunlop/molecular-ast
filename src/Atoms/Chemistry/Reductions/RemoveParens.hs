{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Chemistry.Reductions.RemoveParens where
import Atoms.Elements.Parens
import Atoms.Elements.Not
import Atoms.Elements.Or
import Atoms.Molecule.AST
import Data.Type.Equality
import Hyper
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF

class RemoveParens f t where
    removeParens :: VariantF f (Pure # Molecule (VariantF t))
                 -> Pure # Molecule (VariantF t)

instance ( HasF Parens f
         , ForAllIn Functor t
         , Insert Parens t ~ f
         , Follow (Locate Parens f) f ~ Parens
         , FromSides (Locate Parens f)
         ) => RemoveParens f t where
    removeParens (VariantF (tag :: SSide ss) res) = 
        case (testEquality tag (fromSides @(Locate Parens f)), proveFollowInsert @ss @Parens @t) of
            (Just Refl, HRefl) -> case res of
                                      Parens expr -> expr 
            (Nothing, HRefl) -> Pure $ Molecule $ VariantF tag res 


