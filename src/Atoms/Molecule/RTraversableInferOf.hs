{-# LANGUAGE FlexibleInstances    #-}
module Atoms.Molecule.RTraversableInferOf where
import Atoms.Molecule.AST
import Atoms.Molecule.InferOf
import Atoms.Molecule.Recursively
import Atoms.Molecule.RTraversable
import Hyper.Infer
import Type.Set.VariantF

instance RTraversableInferOf (Molecule (VariantF g))

