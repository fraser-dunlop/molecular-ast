{-# LANGUAGE TemplateHaskell      #-}
module Atoms.Molecule.AST where 
import Hyper
import Hyper.TH.Traversable

-- | A Molecule is an AST composed from a set of Atoms
-- e.g. Molecule (VariantF atoms) h
data Molecule g h where
  Molecule :: (Functor g) => g (h :# Molecule g) -> Molecule g h

makeHTraversableAndBases ''Molecule

