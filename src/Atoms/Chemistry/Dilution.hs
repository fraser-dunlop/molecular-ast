{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Chemistry.Dilution where
import Atoms.Molecule.AST
import Atoms.Elements.Generic.Type
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
      , Insert d f ~ t
      ) => Dilution d f t where
    dilute1 :: Proxy d
            -> VariantF f (Pure # Molecule (VariantF t))
            -> Pure # Molecule (VariantF t)
    dilute :: Proxy d
           -> Pure # Molecule (VariantF f)
           -> Pure # Molecule (VariantF t)

instance ( ForAllIn Functor f
         , ForAllIn Foldable f
         , ForAllIn Traversable f
         , ForAllIn Functor t
         , Insert d f ~ t
         ) => Dilution d f t where
    dilute1 _ (VariantF (tag :: SSide ss) res) = 
       case (proveFollowInsert @ss @d @(Insert d f), proveFollowInsert @ss @d @f) of
           (HRefl, HRefl) -> Pure $ Molecule $ VariantF tag res 
    dilute prox molecule = foldMolecule (dilute1 prox) molecule 


