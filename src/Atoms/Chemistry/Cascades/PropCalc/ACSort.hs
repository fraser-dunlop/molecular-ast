{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Chemistry.Cascades.PropCalc.ACSort where
import Atoms.Chemistry.Transformations.PropCalc.ACSort
import Atoms.Chemistry.Utils.FixedPoint
import Atoms.Molecule.AST
import Data.Type.Equality
import Hyper
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF

class ACSort t => ACSortCascades t where
    aCSortFixed :: (Pure # Molecule (VariantF t))
                        -> ((Bool, Int), (Pure # Molecule (VariantF t)))



instance ACSort t => ACSortCascades t where
    aCSortFixed molecule =
        fixedPointCounted aCSort molecule


