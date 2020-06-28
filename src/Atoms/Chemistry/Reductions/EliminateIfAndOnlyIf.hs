{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Chemistry.Reductions.EliminateIfAndOnlyIf where
import Atoms.Elements.And
import Atoms.Elements.IfAndOnlyIf
import Atoms.Elements.Not
import Atoms.Elements.Or
import Atoms.Molecule.AST
import Data.Type.Equality
import Hyper
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF

class EliminateIfAndOnlyIf f t where
    eliminateIfAndOnlyIf :: VariantF f (Pure # Molecule (VariantF t))
                         -> Pure # Molecule (VariantF t)


instance ( HasF IfAndOnlyIf f
         , ForAllIn Functor t
         , Insert IfAndOnlyIf t ~ f
         , Follow (Locate IfAndOnlyIf f) f ~ IfAndOnlyIf
         , FromSides (Locate IfAndOnlyIf f)
         , HasF Or t
         , HasF Not t
         , HasF And t
         ) => EliminateIfAndOnlyIf f t where
    eliminateIfAndOnlyIf (VariantF (tag :: SSide ss) res) = 
        case (testEquality tag (fromSides @(Locate IfAndOnlyIf f)), proveFollowInsert @ss @IfAndOnlyIf @t) of
            (Just Refl, HRefl) -> case res of
                                      IfAndOnlyIf a b -> (a `iOr` (iNot b)) `iAnd` ((iNot a) `iOr` b)
            (Nothing, HRefl) -> Pure $ Molecule $ VariantF tag res 


