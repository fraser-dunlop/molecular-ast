{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Chemistry.Cascades.PropCalc.DoubleNegation where
import Atoms.Chemistry.Transformations.PropCalc.DoubleNegation
import Atoms.Chemistry.Utils.FixedPoint
import Atoms.Molecule.AST
import Data.Type.Equality
import Hyper
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF

class DoubleNegation t => DoubleNegationCascades t where
    doubleNegationFixed :: (Pure # Molecule (VariantF t))
                        -> ((Bool, Int), (Pure # Molecule (VariantF t)))



instance DoubleNegation t => DoubleNegationCascades t where
    doubleNegationFixed molecule =
        fixedPointCounted doubleNegation molecule


