{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Chemistry.Reductions.EliminateImplies where
import Atoms.Elements.FOL.Implies
import Atoms.Elements.FOL.Not
import Atoms.Elements.FOL.Or
import Atoms.Molecule.AST
import Data.Type.Equality
import Hyper
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF
import Data.STRef
import Control.Monad.ST

class ( HasF Implies f
      , HasF Or t
      , HasF Not t
      , ForAllIn Functor f
      , ForAllIn Foldable f
      , ForAllIn Traversable f
      , ForAllIn Functor t
      , Insert Implies t ~ f
      , Follow (Locate Implies f) f ~ Implies
      , FromSides (Locate Implies f)
      ) => EliminateImplies f t where
    eliminateImplies1 :: STRef s Bool
                      -> VariantF f (Pure # Molecule (VariantF t))
                      -> ST s (Pure # Molecule (VariantF t))
    eliminateImplies :: Pure # Molecule (VariantF f)
                     -> (Bool, Pure # Molecule (VariantF t))

instance ( HasF Implies f
         , HasF Or t
         , HasF Not t
         , ForAllIn Functor f
         , ForAllIn Foldable f
         , ForAllIn Traversable f
         , ForAllIn Functor t
         , Insert Implies t ~ f
         , Follow (Locate Implies f) f ~ Implies
         , FromSides (Locate Implies f)
         ) => EliminateImplies f t where
    eliminateImplies1 changed (VariantF (tag :: SSide ss) res) = 
        case (testEquality tag (fromSides @(Locate Implies f)), proveFollowInsert @ss @Implies @t) of
            (Just Refl, HRefl) -> case res of
                                      Implies a b -> do
                                         writeSTRef changed True
                                         pure ((iNot a) `iOr` b) 
            (Nothing, HRefl) -> pureVNode $ VariantF tag res 
    eliminateImplies molecule = runST $ do
        changed <- newSTRef False
        res <- foldMoleculeM (eliminateImplies1 changed) molecule
        cha <- readSTRef changed
        return (cha, res)


