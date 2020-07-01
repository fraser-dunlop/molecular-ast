{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Chemistry.Transformations.PropCalc.Idempotency where
import Atoms.Elements.Generic.Variable
import Atoms.Elements.PropCalc.And
import Atoms.Elements.PropCalc.Not
import Atoms.Elements.PropCalc.Or
import Atoms.Molecule.AST
import Data.Type.Equality
import Hyper
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF
import Data.STRef
import Control.Monad.ST

-- If we were in an ACSE context (some other wrapper than Pure) implementing the needful
-- then this could eliminate entire expressions before introducing new lettings for them.
-- This implementation just works on Variable name equality.
-- p /\ p == p 
-- p \/ p == p 
-- !p /\ !p == !p 
-- !p \/ !p == !p 

class ( HasF And t
      , HasF Not t
      , HasF Or t
      , HasF Variable t
      , ForAllIn Functor t
      , ForAllIn Foldable t
      , ForAllIn Traversable t
      , Follow (Locate And t) t ~ And 
      , FromSides (Locate And t)
      , Follow (Locate Not t) t ~ Not 
      , FromSides (Locate Not t)
      , Follow (Locate Or t) t ~ Or 
      , FromSides (Locate Or t)
      , Follow (Locate Variable t) t ~ Variable
      , FromSides (Locate Variable t)
      ) => Idempotency t where
    idempotencyElimination ::  STRef s Bool
                         -> VariantF t (Pure # Molecule (VariantF t))
                         -> ST s (Pure # Molecule (VariantF t))

-- these rules are just pattern matching with proofs. All this could be done with TemplateHaskell!!!
--
-- this is just a fancy way of saying this generically for Molecules
--
--transformation Idempotency where
--    idempotencyElimination (And (Variable l) (Variable r)) = Variable r
--    idempotencyElimination (And (Not (Variable l)) (Not (Variable r))) = Variable r
--    idempotencyElimination (Or (Variable l) (Variable r)) = Variable r
--    idempotencyElimination (Or (Not (Variable l)) (Not (Variable r))) = Variable r
--    idempotencyElimination n = n



instance ( HasF And t
         , HasF Not t
         , HasF Or t
         , HasF Variable t
         , ForAllIn Functor t
         , ForAllIn Foldable t
         , ForAllIn Traversable t
         , Follow (Locate And t) t ~ And 
         , FromSides (Locate And t)
         , Follow (Locate Not t) t ~ Not 
         , FromSides (Locate Not t)
         , Follow (Locate Or t) t ~ Or 
         , FromSides (Locate Or t)
         , Follow (Locate Variable t) t ~ Variable
         , FromSides (Locate Variable t)
         ) => Idempotency t where
    idempotencyElimination changed v@(VariantF tag res) =
        case testEquality tag (fromSides @(Locate And t)) of
          Just Refl ->
            case res of
              And (Pure (Molecule l@(VariantF tagl resl))) (Pure (Molecule r@(VariantF tagr resr))) ->
                case ( testEquality tagl (fromSides @(Locate Variable t))
                     , testEquality tagr (fromSides @(Locate Variable t))) of
                  (Just Refl, Just Refl) ->
                     case (resl, resr) of
                       (Variable vl, Variable vr) ->
                         if vl == vr
                           then do
                             writeSTRef changed True
                             pure $ iVariable vl 
                           else pureVNode v
                  (Nothing,Nothing) -> 
                    case ( testEquality tagl (fromSides @(Locate Not t))
                         , testEquality tagr (fromSides @(Locate Not t))) of
                      (Just Refl, Just Refl) ->
                         case (resl, resr) of
                           ( Not (Pure (Molecule nl@(VariantF tagnl resnl)))
                            , Not (Pure (Molecule nr@(VariantF tagnr resnr)))) ->
                             case ( testEquality tagnl (fromSides @(Locate Variable t))
                                  , testEquality tagnr (fromSides @(Locate Variable t))) of
                               (Just Refl, Just Refl) ->
                                 case (resnl, resnr) of
                                   (Variable vl, Variable vr) ->
                                     if vl == vr
                                       then do
                                         writeSTRef changed True
                                         pure $ iNot $ iVariable vl 
                                       else pureVNode v 
                               (_,_) -> pureVNode v
                      (_,_) -> pureVNode v
                  (_,_) -> pureVNode v
          Nothing -> 
            case testEquality tag (fromSides @(Locate Or t)) of
              Just Refl ->
                case res of
                  Or (Pure (Molecule l@(VariantF tagl resl))) (Pure (Molecule r@(VariantF tagr resr))) ->
                    case ( testEquality tagl (fromSides @(Locate Variable t))
                         , testEquality tagr (fromSides @(Locate Variable t))) of
                      (Just Refl, Just Refl) ->
                         case (resl, resr) of
                           (Variable vl, Variable vr) ->
                             if vl == vr
                               then do
                                 writeSTRef changed True
                                 pure $ iVariable vl 
                               else pureVNode v
                      (Nothing, Nothing) -> 
                        case ( testEquality tagl (fromSides @(Locate Not t))
                             , testEquality tagr (fromSides @(Locate Not t))) of
                          (Just Refl, Just Refl) ->
                             case (resl, resr) of
                               ( Not (Pure (Molecule nl@(VariantF tagnl resnl)))
                                , Not (Pure (Molecule nr@(VariantF tagnr resnr)))) ->
                                 case ( testEquality tagnl (fromSides @(Locate Variable t))
                                      , testEquality tagnr (fromSides @(Locate Variable t))) of
                                   (Just Refl, Just Refl) ->
                                     case (resnl, resnr) of
                                       (Variable vl, Variable vr) ->
                                         if vl == vr
                                           then do
                                             writeSTRef changed True
                                             pure $ iNot $ iVariable vl 
                                           else pureVNode v 
                                   (_,_) -> pureVNode v
                          (_,_) -> pureVNode v
                      (_,_) -> pureVNode v
              Nothing -> pureVNode v 



