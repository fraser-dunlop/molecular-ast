{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Chemistry.Cascades.PropCalc.DeMorgan where
import Atoms.Chemistry.Transformations.PropCalc.DeMorgan
import Atoms.Chemistry.Utils.FixedPoint
import Atoms.Molecule.AST
import Data.Type.Equality
import Hyper
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF

class DeMorgan t => DeMorganCascades t where
    deMorganNegationOfDisjunctionFixed :: (Pure # Molecule (VariantF t))
                                       -> ((Bool, Int), (Pure # Molecule (VariantF t)))
    deMorganNegationOfConjunctionFixed :: (Pure # Molecule (VariantF t))
                                       -> ((Bool, Int), (Pure # Molecule (VariantF t)))




instance DeMorgan t => DeMorganCascades t where
    deMorganNegationOfDisjunctionFixed molecule =
        fixedPointCounted deMorganNegationOfDisjunction molecule
    deMorganNegationOfConjunctionFixed molecule =
        fixedPointCounted deMorganNegationOfConjunction molecule


