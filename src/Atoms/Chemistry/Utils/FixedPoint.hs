{-# LANGUAGE FlexibleContexts     #-}
module Atoms.Chemistry.Utils.FixedPoint
    ( fixedPointCounted
    ) where
import Atoms.Molecule.AST
import Hyper
import Type.Set.Variant
import Type.Set.VariantF
import Data.STRef
import Control.Monad.ST

fixedPointCounter :: forall s g . (ForAllIn Functor g, ForAllIn Foldable g, ForAllIn Traversable g)
                  => (STRef s Bool
                              -> VariantF g (Pure # Molecule (VariantF g))
                              -> ST s (Pure # Molecule (VariantF g)))
                  -> (Pure # Molecule (VariantF g))
                  -> STRef s Bool
                  -> STRef s Int
                  -> ST s (Pure # Molecule (VariantF g))
fixedPointCounter transformation molecule changed counter = do
        change_detect <- newSTRef False
        transformed <- foldMoleculeM (transformation change_detect) molecule
        has_changed <- readSTRef change_detect
        modifySTRef counter (+ 1) 
        if has_changed
           then do
               writeSTRef changed True
               fixedPointCounter transformation transformed changed counter
           else pure $ transformed
 

fixedPointCounted :: forall g . (ForAllIn Functor g, ForAllIn Foldable g, ForAllIn Traversable g)
                  => (forall s . STRef s Bool
                                 -> VariantF g (Pure # Molecule (VariantF g))
                                 -> ST s (Pure # Molecule (VariantF g)))
                  -> (Pure # Molecule (VariantF g))
                  -> ((Bool, Int), Pure # Molecule (VariantF g))
fixedPointCounted transformation molecule =
    runST $ do
        changed <- newSTRef False
        counter <- newSTRef 0
        transformed <- fixedPointCounter transformation molecule changed counter
        count <- (,) <$> readSTRef changed <*> readSTRef counter
        pure (count, transformed)
 

