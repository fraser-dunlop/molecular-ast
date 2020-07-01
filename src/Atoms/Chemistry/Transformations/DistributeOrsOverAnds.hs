{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Chemistry.Transformations.DistributeOrsOverAnds where
import Atoms.Elements.And
import Atoms.Elements.Or
import Atoms.Molecule.AST
import Data.Type.Equality
import Hyper
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF
import Data.STRef
import Control.Monad.ST

class ( HasF And t
      , HasF Or t
      , ForAllIn Functor t
      , ForAllIn Foldable t
      , ForAllIn Traversable t
      , Follow (Locate And t) t ~ And 
      , FromSides (Locate And t)
      , Follow (Locate Or t) t ~ Or 
      , FromSides (Locate Or t)
      ) => DistributeOrsOverAnds t where
    distributeOrsOverAnds ::  STRef s Bool
                          -> VariantF t (Pure # Molecule (VariantF t))
                          -> ST s (Pure # Molecule (VariantF t))

instance ( HasF And t
         , HasF Or t
         , ForAllIn Functor t
         , ForAllIn Foldable t
         , ForAllIn Traversable t
         , Follow (Locate And t) t ~ And 
         , FromSides (Locate And t)
         , Follow (Locate Or t) t ~ Or 
         , FromSides (Locate Or t)
         ) => DistributeOrsOverAnds t where
    distributeOrsOverAnds changed (VariantF tag res) =
      case testEquality tag (fromSides @(Locate Or t)) of
        Just Refl ->
          case res of
            Or l@(Pure (Molecule (VariantF tagl resl))) r@(Pure (Molecule (VariantF tagr resr))) ->
              case testEquality tagr (fromSides @(Locate And t)) of
                Just Refl ->
                  case resr of
                    And a b -> do
                      writeSTRef changed True
                      pure $ (l `iOr` a) `iAnd` (l `iOr` b)
                Nothing -> case testEquality tagl (fromSides @(Locate And t)) of
                             Just Refl ->
                               case resl of
                                 And a b -> do
                                   writeSTRef changed True
                                   pure $ (a `iOr` r) `iAnd` (b `iOr` r)
                             Nothing -> pure $ Pure $ Molecule (VariantF tag res) 
        Nothing -> pure $ Pure $ Molecule (VariantF tag res)

