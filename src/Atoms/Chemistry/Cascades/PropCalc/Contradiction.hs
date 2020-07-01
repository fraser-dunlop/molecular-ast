{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Chemistry.Cascades.PropCalc.Contradiction where
import Atoms.Chemistry.Transformations.PropCalc.Contradiction
import Atoms.Chemistry.Utils.FixedPoint
import Atoms.Molecule.AST
import Data.Type.Equality
import Hyper
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF

class Contradiction t => ContradictionCascades t where
    contradictionEliminationFixed :: (Pure # Molecule (VariantF t))
                        -> ((Bool, Int), (Pure # Molecule (VariantF t)))



instance Contradiction t => ContradictionCascades t where
    contradictionEliminationFixed molecule =
        fixedPointCounted contradictionElimination molecule


