{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Chemistry.Transformations.FOL.LitBoolElimination where
import Atoms.Elements.FOL.And
import Atoms.Elements.FOL.LitBool
import Atoms.Elements.FOL.Or
import Atoms.Molecule.AST
import Data.Type.Equality
import Hyper
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF
import Data.STRef
import Control.Monad.ST

-- True /\ a == a
-- a /\ True == a
-- False /\ a == False
-- a /\ False = False
--
-- True \/ a = True
-- a \/ True = True
-- False \/ a = a
-- a \/ False = a

class ( HasF And t
      , HasF LitBool t
      , HasF Or t
      , ForAllIn Functor t
      , ForAllIn Foldable t
      , ForAllIn Traversable t
      , Follow (Locate And t) t ~ And
      , FromSides (Locate And t)
      , Follow (Locate LitBool t) t ~ LitBool
      , FromSides (Locate LitBool t)
      , Follow (Locate Or t) t ~ Or 
      , FromSides (Locate Or t)
      ) => LitBoolElimination t where
    litBoolElimination ::  STRef s Bool
                       -> VariantF t (Pure # Molecule (VariantF t))
                       -> ST s (Pure # Molecule (VariantF t))

instance ( HasF And t
         , HasF LitBool t
         , HasF Or t
         , ForAllIn Functor t
         , ForAllIn Foldable t
         , ForAllIn Traversable t
         , Follow (Locate And t) t ~ And
         , FromSides (Locate And t)
         , Follow (Locate LitBool t) t ~ LitBool
         , FromSides (Locate LitBool t)
         , Follow (Locate Or t) t ~ Or 
         , FromSides (Locate Or t)
         ) => LitBoolElimination t where
    litBoolElimination changed v@(VariantF tag res) =
        case testEquality tag (fromSides @(Locate And t)) of
          Just Refl ->
            case res of
              And (Pure (Molecule l@(VariantF tagl resl))) (Pure (Molecule r@(VariantF tagr resr))) ->
                case testEquality tagl (fromSides @(Locate LitBool t)) of
                  Just Refl ->
                    case resl of
                      LitBool True -> do 
                        writeSTRef changed True
                        pureVNode r 
                      LitBool False -> do 
                        writeSTRef changed True
                        pureVNode l
                  Nothing ->
                    case testEquality tagr (fromSides @(Locate LitBool t)) of
                      Just Refl -> 
                        case resr of
                          LitBool True -> do 
                            writeSTRef changed True
                            pureVNode l 
                          LitBool False -> do 
                            writeSTRef changed True
                            pureVNode r 
                      Nothing -> pure $ Pure $ Molecule (VariantF tag res) 
          Nothing -> 
            case testEquality tag (fromSides @(Locate Or t)) of
              Just Refl -> 
                case res of
                  Or (Pure (Molecule l@(VariantF tagl resl))) (Pure (Molecule r@(VariantF tagr resr))) ->
                    case testEquality tagl (fromSides @(Locate LitBool t)) of
                      Just Refl ->
                        case resl of
                          LitBool True -> do 
                            writeSTRef changed True
                            pureVNode l 
                          LitBool False -> do 
                            writeSTRef changed True
                            pureVNode r
                      Nothing ->
                        case testEquality tagr (fromSides @(Locate LitBool t)) of
                          Just Refl -> 
                            case resr of
                              LitBool True -> do 
                                writeSTRef changed True
                                pureVNode r 
                              LitBool False -> do 
                                writeSTRef changed True
                                pureVNode l 
                          Nothing -> pure $ Pure $ Molecule (VariantF tag res) 
              Nothing -> pureVNode v 


