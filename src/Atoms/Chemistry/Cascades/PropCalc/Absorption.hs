{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Chemistry.Cascades.PropCalc.Absorption where
import Atoms.Chemistry.Transformations.PropCalc.Absorption
import Atoms.Chemistry.Utils.FixedPoint
import Atoms.Molecule.AST
import Data.Type.Equality
import Hyper
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF

class Absorption t => AbsorptionCascades t where
    absorptionFixed :: (Pure # Molecule (VariantF t))
                        -> ((Bool, Int), (Pure # Molecule (VariantF t)))



instance Absorption t => AbsorptionCascades t where
    absorptionFixed molecule =
        fixedPointCounted absorption molecule


