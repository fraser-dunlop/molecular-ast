{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Chemistry.Cascades.FOL.LitBoolElimination where
import Atoms.Chemistry.Transformations.FOL.LitBoolElimination
import Atoms.Chemistry.Utils.FixedPoint
import Atoms.Molecule.AST
import Data.Type.Equality
import Hyper
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF

class LitBoolElimination t => LitBoolEliminationCascades t where
    litBoolEliminationFixed :: (Pure # Molecule (VariantF t))
                        -> ((Bool, Int), (Pure # Molecule (VariantF t)))



instance LitBoolElimination t => LitBoolEliminationCascades t where
    litBoolEliminationFixed molecule =
        fixedPointCounted litBoolElimination molecule


