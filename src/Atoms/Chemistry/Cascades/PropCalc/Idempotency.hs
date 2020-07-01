{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Chemistry.Cascades.PropCalc.Idempotency where
import Atoms.Chemistry.Transformations.PropCalc.Idempotency
import Atoms.Chemistry.Utils.FixedPoint
import Atoms.Molecule.AST
import Data.Type.Equality
import Hyper
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF

class Idempotency t => IdempotencyCascades t where
    idempotencyFixed :: (Pure # Molecule (VariantF t))
                        -> ((Bool, Int), (Pure # Molecule (VariantF t)))



instance Idempotency t => IdempotencyCascades t where
    idempotencyFixed molecule =
        fixedPointCounted idempotencyElimination molecule


