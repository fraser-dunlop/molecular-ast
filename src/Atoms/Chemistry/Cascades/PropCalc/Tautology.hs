{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Chemistry.Cascades.PropCalc.Tautology where
import Atoms.Chemistry.Transformations.PropCalc.Tautology
import Atoms.Chemistry.Utils.FixedPoint
import Atoms.Molecule.AST
import Data.Type.Equality
import Hyper
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF

class Tautology t => TautologyCascades t where
    tautologyFixed :: (Pure # Molecule (VariantF t))
                        -> ((Bool, Int), (Pure # Molecule (VariantF t)))



instance Tautology t => TautologyCascades t where
    tautologyFixed molecule =
        fixedPointCounted tautology molecule


