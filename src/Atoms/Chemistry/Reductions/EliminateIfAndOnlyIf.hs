{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Chemistry.Reductions.EliminateIfAndOnlyIf where
import Atoms.Elements.And
import Atoms.Elements.IfAndOnlyIf
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

class ( HasF IfAndOnlyIf f
      , HasF Or t
      , HasF Not t
      , HasF And t
      , ForAllIn Functor t
      , ForAllIn Functor f
      , ForAllIn Foldable f
      , ForAllIn Traversable f
      , Insert IfAndOnlyIf t ~ f
      , Follow (Locate IfAndOnlyIf f) f ~ IfAndOnlyIf
      , FromSides (Locate IfAndOnlyIf f)
      ) => EliminateIfAndOnlyIf f t where
    eliminateIfAndOnlyIf1 :: STRef s Bool
                          -> VariantF f (Pure # Molecule (VariantF t))
                          -> ST s (Pure # Molecule (VariantF t))
    eliminateIfAndOnlyIf :: Pure # Molecule (VariantF f)
                         -> (Bool, Pure # Molecule (VariantF t))


instance ( HasF IfAndOnlyIf f
         , HasF Or t
         , HasF Not t
         , HasF And t
         , ForAllIn Functor t
         , ForAllIn Functor f
         , ForAllIn Foldable f
         , ForAllIn Traversable f
         , Insert IfAndOnlyIf t ~ f
         , Follow (Locate IfAndOnlyIf f) f ~ IfAndOnlyIf
         , FromSides (Locate IfAndOnlyIf f)
         ) => EliminateIfAndOnlyIf f t where
    eliminateIfAndOnlyIf1 changed (VariantF (tag :: SSide ss) res) = 
        case (testEquality tag (fromSides @(Locate IfAndOnlyIf f)), proveFollowInsert @ss @IfAndOnlyIf @t) of
            (Just Refl, HRefl) -> case res of
                                      IfAndOnlyIf a b -> do
                                           writeSTRef changed True
                                           pure ((a `iOr` (iNot b)) `iAnd` ((iNot a) `iOr` b))
            (Nothing, HRefl) -> pureVNode $ VariantF tag res 
    eliminateIfAndOnlyIf molecule = runST $ do
        changed <- newSTRef False
        res <- foldMoleculeM (eliminateIfAndOnlyIf1 changed) molecule
        cha <- readSTRef changed
        return (cha, res)



