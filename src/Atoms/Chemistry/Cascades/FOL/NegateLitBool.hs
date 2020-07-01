{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Chemistry.Cascades.FOL.NegateLitBool where
import Atoms.Chemistry.Transformations.FOL.NegateLitBool
import Atoms.Chemistry.Utils.FixedPoint
import Atoms.Molecule.AST
import Data.Type.Equality
import Hyper
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF

class NegateLitBool t => NegateLitBoolCascades t where
    negateLitBoolFixed :: (Pure # Molecule (VariantF t))
                        -> ((Bool, Int), (Pure # Molecule (VariantF t)))



instance NegateLitBool t => NegateLitBoolCascades t where
    negateLitBoolFixed molecule =
        fixedPointCounted negateLitBool molecule


