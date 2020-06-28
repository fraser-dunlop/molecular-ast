{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
module Atoms.Molecule.Recursively where
import Atoms.Molecule.AST
import Hyper

instance RNodes (Molecule g)
