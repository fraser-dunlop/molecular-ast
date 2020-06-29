{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Chemistry.Cascades.DeMorgan where
import Atoms.Chemistry.Transformations.DeMorgan
import Atoms.Chemistry.Utils.FixedPoint
import Atoms.Elements.And
import Atoms.Elements.Not
import Atoms.Elements.Or
import Atoms.Molecule.AST
import Data.Type.Equality
import Hyper
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF

class DeMorganCascades t where
    deMorganNegationOfDisjunctionFixed :: (Pure # Molecule (VariantF t))
                                       -> ((Bool, Int), (Pure # Molecule (VariantF t)))
    deMorganNegationOfConjunctionFixed :: (Pure # Molecule (VariantF t))
                                       -> ((Bool, Int), (Pure # Molecule (VariantF t)))




instance ( HasF And t
         , HasF Not t
         , HasF Or t
         , ForAllIn Functor t
         , ForAllIn Foldable t
         , ForAllIn Traversable t
         , Follow (Locate And t) t ~ And 
         , FromSides (Locate And t)
         , Follow (Locate Not t) t ~ Not 
         , FromSides (Locate Not t)
         , Follow (Locate Or t) t ~ Or 
         , FromSides (Locate Or t)
         ) => DeMorganCascades t where
    deMorganNegationOfDisjunctionFixed molecule =
        fixedPointCounted deMorganNegationOfDisjunction molecule
    deMorganNegationOfConjunctionFixed molecule =
        fixedPointCounted deMorganNegationOfConjunction molecule


