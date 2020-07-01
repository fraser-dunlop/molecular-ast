{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Chemistry.Cascades.FOL.Tautology where
import Atoms.Chemistry.Transformations.FOL.Tautology
import Atoms.Chemistry.Utils.FixedPoint
import Atoms.Molecule.AST
import Data.Type.Equality
import Hyper
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF

class Tautology t => TautologyCascades t where
    tautologyEliminationFixed :: (Pure # Molecule (VariantF t))
                        -> ((Bool, Int), (Pure # Molecule (VariantF t)))



instance Tautology t => TautologyCascades t where
    tautologyEliminationFixed molecule =
        fixedPointCounted tautologyElimination molecule


