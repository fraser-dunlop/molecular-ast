{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Reductions.EliminateImplies where
import Atoms.Elements.Implies
import Atoms.Elements.Not
import Atoms.Elements.Or
import Atoms.Molecule.AST
import Data.Type.Equality
import Hyper
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF

class EliminateImplies f t where
    eliminateImplies :: VariantF f (Pure # Molecule (VariantF t))
                     -> Pure # Molecule (VariantF t)

instance ( HasF Implies f
         , HasF Or t
         , HasF Not t
         , ForAllIn Functor t
         , Insert Implies t ~ f
         , Follow (Locate Implies f) f ~ Implies
         , FromSides (Locate Implies f)
         ) => EliminateImplies f t where
    eliminateImplies (VariantF (tag :: SSide ss) res) = 
        case (testEquality tag (fromSides @(Locate Implies f)), proveFollowInsert @ss @Implies @t) of
            (Just Refl, HRefl) -> case res of
                                      Implies a b -> (iNot a) `iOr` b 
            (Nothing, HRefl) -> Pure $ Molecule $ VariantF tag res 


