{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Chemistry.Transformations.FOL.Tautology where
import Atoms.Elements.FOL.LitBool
import Atoms.Elements.FOL.Not
import Atoms.Elements.FOL.Or
import Atoms.Elements.Generic.Variable
import Atoms.Molecule.AST
import Data.Type.Equality
import Hyper
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF
import Data.STRef
import Control.Monad.ST

-- If we were in an ACSE context (some other wrapper than pure implementing the needful)
-- then this could eliminate entire expressions before introducing new lettings for them.
-- This implementation just works on Variable name equality.
-- p \/ !p == True
-- !p \/ p == True 

class ( HasF LitBool t     
      , HasF Not t
      , HasF Or t
      , HasF Variable t
      , ForAllIn Functor t
      , ForAllIn Foldable t
      , ForAllIn Traversable t
      , Follow (Locate LitBool t) t ~ LitBool 
      , FromSides (Locate LitBool t)
      , Follow (Locate Not t) t ~ Not
      , FromSides (Locate Not t)
      , Follow (Locate Or t) t ~ Or 
      , FromSides (Locate Or t)
      , Follow (Locate Variable t) t ~ Variable
      , FromSides (Locate Variable t)
      ) => Tautology t where
    tautologyElimination ::  STRef s Bool
                         -> VariantF t (Pure # Molecule (VariantF t))
                         -> ST s (Pure # Molecule (VariantF t))

instance ( HasF LitBool t
         , HasF Not t
         , HasF Or t
         , HasF Variable t
         , ForAllIn Functor t
         , ForAllIn Foldable t
         , ForAllIn Traversable t
         , Follow (Locate LitBool t) t ~ LitBool 
         , FromSides (Locate LitBool t)
         , Follow (Locate Not t) t ~ Not
         , FromSides (Locate Not t)
         , Follow (Locate Or t) t ~ Or 
         , FromSides (Locate Or t)
         , Follow (Locate Variable t) t ~ Variable
         , FromSides (Locate Variable t)
         ) => Tautology t where
    tautologyElimination changed v@(VariantF tag res) =
        case testEquality tag (fromSides @(Locate Or t)) of
          Just Refl ->
            case res of
              Or (Pure (Molecule l@(VariantF tagl resl))) (Pure (Molecule r@(VariantF tagr resr))) ->
                case testEquality tagl (fromSides @(Locate Not t)) of
                  Just Refl ->
                    case resl of
                      Not (Pure (Molecule xl@(VariantF tagxl resxl))) -> do 
                        case ( testEquality tagxl (fromSides @(Locate Variable t))
                             , testEquality tagr (fromSides @(Locate Variable t))) of
                          (Just Refl, Just Refl) ->
                             case (resxl, resr) of
                               (Variable vl, Variable vr) ->
                                 if vl == vr
                                   then do
                                     writeSTRef changed True
                                     pure $ iLitBool True
                                   else pureVNode v
                          (_,_) -> pureVNode v
                  Nothing ->
                    case testEquality tagr (fromSides @(Locate Not t)) of
                      Just Refl -> 
                        case resr of
                          Not (Pure (Molecule xl@(VariantF tagxr resxr))) -> do 
                            case ( testEquality tagl (fromSides @(Locate Variable t))
                                 , testEquality tagxr (fromSides @(Locate Variable t))) of
                              (Just Refl, Just Refl) ->
                                 case (resl, resxr) of
                                   (Variable vl, Variable vr) ->
                                     if vl == vr
                                       then do
                                         writeSTRef changed True
                                         pure $ iLitBool True
                                   else pureVNode v
                              (_,_) -> pureVNode v
                      Nothing -> pure $ Pure $ Molecule (VariantF tag res) 
          Nothing -> pureVNode v 


