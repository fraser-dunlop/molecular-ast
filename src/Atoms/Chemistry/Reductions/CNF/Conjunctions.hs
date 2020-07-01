{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Chemistry.Reductions.CNF.Conjunctions where
import Atoms.Elements.PropCalc.And
import Atoms.Elements.CNF.Conjunction
import Atoms.Molecule.AST
import Data.Type.Equality
import Hyper
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF
import Data.STRef
import Control.Monad.ST

class ( HasF And f
      , HasF Conjunction t
      , ForAllIn Functor t
      , ForAllIn Functor f
      , ForAllIn Foldable f
      , ForAllIn Traversable f
      , Insert And t ~ f
      , Follow (Locate And f) f ~ And
      , FromSides (Locate And f)
      ) => Conjunctions f t where
    conjunctions1 :: STRef s Bool
                 -> VariantF f (Pure # Molecule (VariantF t))
                 -> ST s (Pure # Molecule (VariantF t))
    conjunctions :: Pure # Molecule (VariantF f)
                -> (Bool, Pure # Molecule (VariantF t))


instance ( HasF And f
         , HasF Conjunction t
         , ForAllIn Functor t
         , ForAllIn Functor f
         , ForAllIn Foldable f
         , ForAllIn Traversable f
         , Insert And t ~ f
         , Follow (Locate And f) f ~ And
         , FromSides (Locate And f)
         ) => Conjunctions f t where
    conjunctions1 changed (VariantF (tag :: SSide ss) res) = 
        case (testEquality tag (fromSides @(Locate And f)), proveFollowInsert @ss @And @t) of
            (Just Refl, HRefl) -> case res of
                                      And a b -> do
                                           writeSTRef changed True
                                           pure (iConjunction a b) 
            (Nothing, HRefl) -> pureVNode $ VariantF tag res 
    conjunctions molecule = runST $ do
        changed <- newSTRef False
        res <- foldMoleculeM (conjunctions1 changed) molecule
        cha <- readSTRef changed
        return (cha, res)



