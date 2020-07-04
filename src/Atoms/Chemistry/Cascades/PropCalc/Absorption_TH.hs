{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Chemistry.Cascades.PropCalc.Absorption_TH where
import Atoms.Chemistry.Transformations.PropCalc.Absorption_TH
import Atoms.Chemistry.Utils.FixedPoint
import Atoms.Molecule.AST
import Data.Type.Equality
import Hyper
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF

class AbsorptionTH t => AbsorptionTHCascades t where
    absorptionTHFixed :: (Pure # Molecule (VariantF t))
                        -> ((Bool, Int), (Pure # Molecule (VariantF t)))



instance AbsorptionTH t => AbsorptionTHCascades t where
    absorptionTHFixed molecule =
        fixedPointCounted absorptionTH molecule


