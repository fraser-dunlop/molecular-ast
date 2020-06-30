{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Chemistry.Reductions.CNF.Flatten where
import Atoms.Elements.CNF.Conjunction
import Atoms.Elements.CNF.Disjunction
import Atoms.Elements.CNF.Flattened
import Atoms.Elements.CNF.Literal
import Atoms.Molecule.AST
import Data.Type.Equality
import Hyper
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF
import Control.Monad.ST.Trans
import Control.Monad.Except

class ( HasF Literal f
      , HasF FlatDisjunction t
      , ForAllIn Functor t
      , ForAllIn Functor f
      , ForAllIn Foldable f
      , ForAllIn Traversable f
      , Insert Literal t ~ f
      , Follow (Locate Literal f) f ~ Literal
      , FromSides (Locate Literal f)
      , MonadError String m
      ) => MoveLiteralsIntoFlatDisjunctions m f t where
    moveLiteralsIntoFlatDisjunction1 :: STRef s Bool
                 -> VariantF f (Pure # Molecule (VariantF t))
                 -> STT s m (Pure # Molecule (VariantF t))
    moveLiteralsIntoFlatDisjunction :: Pure # Molecule (VariantF f)
                -> m (Bool, Pure # Molecule (VariantF t))


instance ( HasF Literal f
         , HasF FlatDisjunction t
         , ForAllIn Functor t
         , ForAllIn Functor f
         , ForAllIn Foldable f
         , ForAllIn Traversable f
         , Insert Literal t ~ f
         , Follow (Locate Literal f) f ~ Literal
         , FromSides (Locate Literal f)
         , MonadError String m 
         ) => MoveLiteralsIntoFlatDisjunctions m f t where
    moveLiteralsIntoFlatDisjunction1 changed (VariantF (tag :: SSide ss) res) = 
        case (testEquality tag (fromSides @(Locate Literal f)), proveFollowInsert @ss @Literal @t) of
            (Just Refl, HRefl) -> case res of
                                      _ -> do
                                        writeSTRef changed True
                                        pure $ Pure $ Molecule $ toVariantF $ FlatDisjunctionSingleton res
            (Nothing, HRefl) -> pureVNode $ VariantF tag res 
    moveLiteralsIntoFlatDisjunction molecule = runSTT $ do
        changed <- newSTRef False
        res <- foldMoleculeM (moveLiteralsIntoFlatDisjunction1 changed) molecule
        cha <- readSTRef changed
        return (cha, res)



class ( HasF Disjunction f
      , HasF FlatDisjunction t
      , ForAllIn Functor t
      , ForAllIn Functor f
      , ForAllIn Foldable f
      , ForAllIn Traversable f
      , Insert Disjunction t ~ f
      , Follow (Locate Disjunction f) f ~ Disjunction
      , FromSides (Locate Disjunction f)
      , Follow (Locate FlatDisjunction t) t ~ FlatDisjunction
      , FromSides (Locate FlatDisjunction t)
      , MonadError String m
      ) => MoveDisjunctionsIntoFlatDisjunctions m f t where
    flattenDisjunctions1 :: STRef s Bool
                 -> VariantF f (Pure # Molecule (VariantF t))
                 -> STT s m (Pure # Molecule (VariantF t))
    flattenDisjunctions :: Pure # Molecule (VariantF f)
                -> m (Bool, Pure # Molecule (VariantF t))


instance ( HasF Disjunction f
         , HasF FlatDisjunction t
         , ForAllIn Functor t
         , ForAllIn Functor f
         , ForAllIn Foldable f
         , ForAllIn Traversable f
         , Insert Disjunction t ~ f
         , Follow (Locate Disjunction f) f ~ Disjunction
         , FromSides (Locate Disjunction f)
         , Follow (Locate FlatDisjunction t) t ~ FlatDisjunction
         , FromSides (Locate FlatDisjunction t)
         , MonadError String m 
         ) => MoveDisjunctionsIntoFlatDisjunctions m f t where
    flattenDisjunctions1 changed (VariantF (tag :: SSide ss) res) = 
        case (testEquality tag (fromSides @(Locate Disjunction f)), proveFollowInsert @ss @Disjunction @t) of
            (Just Refl, HRefl) ->
                case res of                 
                   Disjunction (Pure (Molecule (VariantF (tagl :: SSide ssl) resl))) (Pure (Molecule (VariantF (tagr :: SSide ssr) resr))) -> do
                     case (proveFollowInsert @ssl @FlatDisjunction @t, proveFollowInsert @ssl @FlatDisjunction @t) of
                        (HRefl, HRefl) ->  
                           case ( testEquality tagl (fromSides @(Locate FlatDisjunction t))
                                , testEquality tagr (fromSides @(Locate FlatDisjunction t))) of
                               (Just Refl, Just Refl) -> do
                                   writeSTRef changed True
                                   pure $ Pure $ Molecule $ toVariantF $ FlatDisjunctionNode resl resr
                               _ -> throwError "flattenDisjunctions1: expected Disjunction to contain FlatDisjunction Atoms"
            (Nothing, HRefl) -> pureVNode $ VariantF tag res 
    flattenDisjunctions molecule = runSTT $ do
        changed <- newSTRef False
        res <- foldMoleculeM (flattenDisjunctions1 changed) molecule
        cha <- readSTRef changed
        return (cha, res)


class ( HasF FlatDisjunction f
      , HasF FlatConjunction t
      , ForAllIn Functor t
      , ForAllIn Functor f
      , ForAllIn Foldable f
      , ForAllIn Traversable f
      , Insert FlatDisjunction t ~ f
      , Follow (Locate FlatDisjunction f) f ~ FlatDisjunction
      , FromSides (Locate FlatDisjunction f)
      , MonadError String m 
      ) => MoveFlatDisjunctionsIntoFlatConjunctions m f t where
    moveFlatDisjunctionsIntoFlatConjunction1 :: STRef s Bool
                 -> VariantF f (Pure # Molecule (VariantF t))
                 -> STT s m (Pure # Molecule (VariantF t))
    moveFlatDisjunctionsIntoFlatConjunction :: Pure # Molecule (VariantF f)
                -> m (Bool, Pure # Molecule (VariantF t))


instance ( HasF FlatDisjunction f
         , HasF FlatConjunction t
         , ForAllIn Functor t
         , ForAllIn Functor f
         , ForAllIn Foldable f
         , ForAllIn Traversable f
         , Insert FlatDisjunction t ~ f
         , Follow (Locate FlatDisjunction f) f ~ FlatDisjunction
         , FromSides (Locate FlatDisjunction f)
         , MonadError String m 
         ) => MoveFlatDisjunctionsIntoFlatConjunctions m f t where
    moveFlatDisjunctionsIntoFlatConjunction1 changed (VariantF (tag :: SSide ss) res) = 
        case (testEquality tag (fromSides @(Locate FlatDisjunction f)), proveFollowInsert @ss @FlatDisjunction @t) of
            (Just Refl, HRefl) -> case res of
                                      _ -> do
                                        writeSTRef changed True
                                        pure $ Pure $ Molecule $ toVariantF $ FlatConjunctionSingleton res
            (Nothing, HRefl) -> pureVNode $ VariantF tag res 
    moveFlatDisjunctionsIntoFlatConjunction molecule = runSTT $ do
        changed <- newSTRef False
        res <- foldMoleculeM (moveFlatDisjunctionsIntoFlatConjunction1 changed) molecule
        cha <- readSTRef changed
        return (cha, res)



class ( HasF Conjunction f
      , HasF FlatConjunction t
      , ForAllIn Functor t
      , ForAllIn Functor f
      , ForAllIn Foldable f
      , ForAllIn Traversable f
      , Insert Conjunction t ~ f
      , Follow (Locate Conjunction f) f ~ Conjunction
      , FromSides (Locate Conjunction f)
      , Follow (Locate FlatConjunction t) t ~ FlatConjunction
      , FromSides (Locate FlatConjunction t)
      , MonadError String m
      ) => MoveConjunctionsIntoFlatConjunctions m f t where
    flattenConjunctions1 :: STRef s Bool
                 -> VariantF f (Pure # Molecule (VariantF t))
                 -> STT s m (Pure # Molecule (VariantF t))
    flattenConjunctions :: Pure # Molecule (VariantF f)
                -> m (Bool, Pure # Molecule (VariantF t))


instance ( HasF Conjunction f
         , HasF FlatConjunction t
         , ForAllIn Functor t
         , ForAllIn Functor f
         , ForAllIn Foldable f
         , ForAllIn Traversable f
         , Insert Conjunction t ~ f
         , Follow (Locate Conjunction f) f ~ Conjunction
         , FromSides (Locate Conjunction f)
         , Follow (Locate FlatConjunction t) t ~ FlatConjunction
         , FromSides (Locate FlatConjunction t)
         , MonadError String m 
         ) => MoveConjunctionsIntoFlatConjunctions m f t where
    flattenConjunctions1 changed (VariantF (tag :: SSide ss) res) = 
        case (testEquality tag (fromSides @(Locate Conjunction f)), proveFollowInsert @ss @Conjunction @t) of
            (Just Refl, HRefl) ->
                case res of                 
                   Conjunction (Pure (Molecule (VariantF (tagl :: SSide ssl) resl))) (Pure (Molecule (VariantF (tagr :: SSide ssr) resr))) -> do
                     case (proveFollowInsert @ssl @FlatConjunction @t, proveFollowInsert @ssl @FlatConjunction @t) of
                        (HRefl, HRefl) ->  
                           case ( testEquality tagl (fromSides @(Locate FlatConjunction t))
                                , testEquality tagr (fromSides @(Locate FlatConjunction t))) of
                               (Just Refl, Just Refl) -> do
                                   writeSTRef changed True
                                   pure $ Pure $ Molecule $ toVariantF $ FlatConjunctionNode resl resr
                               _ -> throwError "flattenConjunctions1: expected Conjunction to contain FlatConjunction Atoms"
            (Nothing, HRefl) -> pureVNode $ VariantF tag res 
    flattenConjunctions molecule = runSTT $ do
        changed <- newSTRef False
        res <- foldMoleculeM (flattenConjunctions1 changed) molecule
        cha <- readSTRef changed
        return (cha, res)
