{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Chemistry.Reductions.CNF.Disjunctions where
import Atoms.Elements.Or
import Atoms.Elements.CNF.Disjunction
import Atoms.Molecule.AST
import Data.Type.Equality
import Hyper
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF
import Data.STRef
import Control.Monad.ST

class ( HasF Or f
      , HasF Disjunction t
      , ForAllIn Functor t
      , ForAllIn Functor f
      , ForAllIn Foldable f
      , ForAllIn Traversable f
      , Insert Or t ~ f
      , Follow (Locate Or f) f ~ Or
      , FromSides (Locate Or f)
      ) => Disjunctions f t where
    disjunctions1 :: STRef s Bool
                 -> VariantF f (Pure # Molecule (VariantF t))
                 -> ST s (Pure # Molecule (VariantF t))
    disjunctions :: Pure # Molecule (VariantF f)
                -> (Bool, Pure # Molecule (VariantF t))


instance ( HasF Or f
         , HasF Disjunction t
         , ForAllIn Functor t
         , ForAllIn Functor f
         , ForAllIn Foldable f
         , ForAllIn Traversable f
         , Insert Or t ~ f
         , Follow (Locate Or f) f ~ Or
         , FromSides (Locate Or f)
         ) => Disjunctions f t where
    disjunctions1 changed (VariantF (tag :: SSide ss) res) = 
        case (testEquality tag (fromSides @(Locate Or f)), proveFollowInsert @ss @Or @t) of
            (Just Refl, HRefl) -> case res of
                                      Or a b -> do
                                           writeSTRef changed True
                                           pure (iDisjunction a b) 
            (Nothing, HRefl) -> pureVNode $ VariantF tag res 
    disjunctions molecule = runST $ do
        changed <- newSTRef False
        res <- foldMoleculeM (disjunctions1 changed) molecule
        cha <- readSTRef changed
        return (cha, res)



