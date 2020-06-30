{-# LANGUAGE DeriveTraversable    #-}
module Atoms.Elements.CNF.Flattened where
import Atoms.Elements.CNF.Literal
import GHC.Generics

data FlatDisjunction h where
   FlatDisjunctionSingleton :: Literal h -> FlatDisjunction h
   FlatDisjunctionNode :: FlatDisjunction h -> FlatDisjunction h -> FlatDisjunction h
   deriving (Eq, Ord, Generic, Generic1, Foldable, Traversable) 

instance Functor FlatDisjunction where
   fmap f (FlatDisjunctionSingleton lit) = FlatDisjunctionSingleton (fmap f lit)
   fmap f (FlatDisjunctionNode left right) = FlatDisjunctionNode (fmap f left) (fmap f right)

data FlatConjunction h where
   FlatConjunctionSingleton :: FlatDisjunction h -> FlatConjunction h
   FlatConjunctionNode :: FlatConjunction h -> FlatConjunction h -> FlatConjunction h
   deriving (Eq, Ord, Generic, Generic1, Foldable, Traversable) 


instance Functor FlatConjunction where
   fmap f (FlatConjunctionSingleton lit) = FlatConjunctionSingleton (fmap f lit)
   fmap f (FlatConjunctionNode left right) = FlatConjunctionNode (fmap f left) (fmap f right)


