{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Chemistry.Reductions.RemoveParens where
import Atoms.Elements.Parens
import Atoms.Elements.Not
import Atoms.Elements.Or
import Atoms.Molecule.AST
import Data.Type.Equality
import Hyper
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF
import Data.STRef
import Control.Monad.ST

class ( HasF Parens f
      , ForAllIn Functor f
      , ForAllIn Foldable f
      , ForAllIn Traversable f
      , ForAllIn Functor t
      , Insert Parens t ~ f
      , Follow (Locate Parens f) f ~ Parens
      , FromSides (Locate Parens f)
      ) => RemoveParens f t where
    removeParens1 :: STRef s Bool
                  -> VariantF f (Pure # Molecule (VariantF t))
                  -> ST s (Pure # Molecule (VariantF t))
    removeParens :: Pure # Molecule (VariantF f)
                 -> (Bool, Pure # Molecule (VariantF t))

instance ( HasF Parens f
         , ForAllIn Functor f
         , ForAllIn Foldable f
         , ForAllIn Traversable f
         , ForAllIn Functor t
         , Insert Parens t ~ f
         , Follow (Locate Parens f) f ~ Parens
         , FromSides (Locate Parens f)
         ) => RemoveParens f t where
    removeParens1 changed (VariantF (tag :: SSide ss) res) = 
        case (testEquality tag (fromSides @(Locate Parens f)), proveFollowInsert @ss @Parens @t) of
            (Just Refl, HRefl) -> case res of
                                      Parens expr -> do
                                          writeSTRef changed True
                                          pure expr 
            (Nothing, HRefl) -> pureVNode $ VariantF tag res 
    removeParens molecule = runST $ do
         changed <- newSTRef False
         res <- foldMoleculeM (removeParens1 changed) molecule 
         cha <- readSTRef changed
         return (cha, res)


