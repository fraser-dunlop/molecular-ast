{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Chemistry.Cascades.DeMorgan where
import Atoms.Chemistry.Transformations.DeMorgan
import Atoms.Elements.And
import Atoms.Elements.Not
import Atoms.Elements.Or
import Atoms.Molecule.AST
import Data.Type.Equality
import Hyper
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF

class DeMorganCascade t where
    deMorganCascade :: Pure # Molecule (VariantF t)
                    -> Pure # Molecule (VariantF t)

instance ( HasF And t
         , HasF Not t
         , HasF Or t
         , ForAllIn Functor t
         , Follow (Locate And t) t ~ And 
         , FromSides (Locate And t)
         , Follow (Locate Not t) t ~ Not 
         , FromSides (Locate Not t)
         , Follow (Locate Or t) t ~ Or 
         , FromSides (Locate Or t)
         ) => DeMorganCascade t where
    deMorganCascade mol = foldMolecule deMorganNegationOfDisjunction (foldMolecule deMorganNegationOfConjunction mol) 

