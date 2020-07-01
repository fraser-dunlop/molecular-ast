{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Chemistry.Cascades.PropCalc.DistributeOrsOverAnds where
import Atoms.Chemistry.Transformations.PropCalc.DistributeOrsOverAnds
import Atoms.Chemistry.Utils.FixedPoint
import Atoms.Molecule.AST
import Data.Type.Equality
import Hyper
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF

class DistributeOrsOverAnds t => DistributeOrsOverAndsCascades t where
    distributeOrsOverAndsFixed :: (Pure # Molecule (VariantF t))
                               -> ((Bool, Int), (Pure # Molecule (VariantF t)))

instance DistributeOrsOverAnds t => DistributeOrsOverAndsCascades t where
    distributeOrsOverAndsFixed molecule =
        fixedPointCounted distributeOrsOverAnds molecule


