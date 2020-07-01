{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Chemistry.Cascades.PropCalc.DominationAndIdentity where
import Atoms.Chemistry.Transformations.PropCalc.DominationAndIdentity
import Atoms.Chemistry.Utils.FixedPoint
import Atoms.Molecule.AST
import Data.Type.Equality
import Hyper
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF

class DominationAndIdentity t => DominationAndIdentityCascades t where
    dominationAndIdentityFixed :: (Pure # Molecule (VariantF t))
                        -> ((Bool, Int), (Pure # Molecule (VariantF t)))



instance DominationAndIdentity t => DominationAndIdentityCascades t where
    dominationAndIdentityFixed molecule =
        fixedPointCounted dominationAndIdentity molecule


