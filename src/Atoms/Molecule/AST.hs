{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE TemplateHaskell      #-}
module Atoms.Molecule.AST where 
import Hyper
import Hyper.TH.Traversable
import Type.Set.Variant
import Type.Set.VariantF


-- | A Molecule is an AST composed from a set of Atoms
-- e.g. Molecule (VariantF atoms) h
data Molecule g h where
  Molecule :: (Functor g) => g (h :# Molecule g) -> Molecule g h

makeHTraversableAndBases ''Molecule

foldMolecule :: (ForAllIn Functor f) => ((VariantF f) a -> a) -> Pure # (Molecule (VariantF f)) -> a
foldMolecule f (Pure (Molecule t)) = f (fmap (foldMolecule f) t)
