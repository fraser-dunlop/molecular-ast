{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
module Atoms.Molecule.RNodes where
import Atoms.Molecule.Recursively
import Atoms.Molecule.AST
import Hyper
import Type.Set.VariantF

instance c (Molecule (VariantF g)) => Recursively c (Molecule (VariantF g))

