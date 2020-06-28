{-# LANGUAGE FlexibleInstances    #-}
module Atoms.Molecule.HasInferredType where
import Atoms.Molecule.AST
import Atoms.Molecule.InferOf
import Hyper
import Hyper.Infer
import Type.Set.VariantF

instance HasInferredType (Molecule (VariantF g)) where
    type TypeOf (Molecule (VariantF g)) = (Molecule (VariantF g))
    inferredType _ = _ANode


