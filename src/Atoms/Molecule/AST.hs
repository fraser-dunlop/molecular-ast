{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE DeriveDataTypeable   #-}
module Atoms.Molecule.AST where 
import Hyper
import Hyper.TH.Traversable
import Type.Set.Variant
import Type.Set.VariantF
import Data.Data

-- | A Molecule is an AST composed from a set of Atoms
-- e.g. Molecule (VariantF atoms) h
data Molecule g h where
  Molecule :: g (h :# Molecule g) -> Molecule g h
  deriving (Generic)

makeHTraversableAndBases ''Molecule

foldMolecule :: (ForAllIn Functor f) => ((VariantF f) a -> a) -> Pure # (Molecule (VariantF f)) -> a
foldMolecule f (Pure (Molecule t)) = f (fmap (foldMolecule f) t)

pureVNode :: ( Applicative m
             , ForAllIn Functor g
             ) => VariantF g (Pure # Molecule (VariantF g))
               -> m (Pure # Molecule (VariantF g)) 
pureVNode = pure . Pure . Molecule

foldMoleculeM :: forall g m a . 
               ( ForAllIn Functor g
               , Monad m
               , ForAllIn Foldable g
               , ForAllIn Traversable g
               ) => ((VariantF g) a -> m a)
                 -> Pure # (Molecule (VariantF g))
                 -> m a
foldMoleculeM f (Pure (Molecule t)) =
    traverse (foldMoleculeM f) t >>= f

