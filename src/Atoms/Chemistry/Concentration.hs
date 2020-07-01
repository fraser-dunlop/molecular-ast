{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Chemistry.Concentration where
import Atoms.Molecule.AST
import Atoms.Elements.Type
import Data.Proxy
import Data.Type.Equality
import Hyper
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF

class ( ForAllIn Functor f
      , ForAllIn Foldable f
      , ForAllIn Traversable f
      , ForAllIn Functor t
      , Insert d t ~ f
      ) => Concentration d f t where
    concentrate1 :: Proxy d
            -> VariantF f (Pure # Molecule (VariantF t))
            -> Pure # Molecule (VariantF t)
    concentrate :: Proxy d
           -> Pure # Molecule (VariantF f)
           -> Pure # Molecule (VariantF t)

instance ( ForAllIn Functor f
         , ForAllIn Foldable f
         , ForAllIn Traversable f
         , ForAllIn Functor t
         , Insert d t ~ f
         ) => Concentration d f t where
    concentrate1 _ (VariantF (tag :: SSide ss) res) = 
       case (proveFollowInsert @ss @d @(Insert d t), proveFollowInsert @ss @d @t) of
           (HRefl, HRefl) -> Pure $ Molecule $ VariantF tag res 
    concentrate prox molecule = foldMolecule (concentrate1 prox) molecule 


