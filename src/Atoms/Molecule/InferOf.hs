{-# LANGUAGE FlexibleInstances    #-}
module Atoms.Molecule.InferOf where
import Atoms.Molecule.AST
import Atoms.Molecule.InferScope
import Hyper
import Hyper.Infer
import Type.Set.VariantF

type instance InferOf (Molecule (VariantF g)) = ANode (Molecule (VariantF g)) 
