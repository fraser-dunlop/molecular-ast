{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
module Atoms.Molecule.RTraversable where
import Atoms.Molecule.AST
import Atoms.Molecule.Recursively
import Atoms.Molecule.RNodes
import Atoms.Molecule.InferScope
import Hyper
import Hyper.Infer
import Type.Set.Variant
import Type.Set.VariantF

instance (ForAllIn Functor g, ForAllIn Foldable g, ForAllIn Traversable g)
     => RTraversable (Molecule (VariantF g))
