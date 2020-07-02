{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Chemistry.Transformations.PropCalc.Absorption where
import Atoms.Elements.Generic.Variable
import Atoms.Elements.PropCalc.And
import Atoms.Elements.PropCalc.Or
import Atoms.Molecule.AST
import Data.Type.Equality
import Hyper
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF
import Data.STRef
import Control.Monad.ST

-- Absorption 
-- p /\ (p \/ _) == p
-- p /\ (_ \/ p) == p
-- (p \/ _) /\ p == p
-- (_ \/ p) /\ p == p
--
-- p \/ (p /\ _) == p
-- p \/ (_ /\ p) == p
-- (p /\ _) \/ p == p
-- (_ /\ p) \/ p == p


-- this is screaming out for TH especially since we want to do this for !p as well as p
-- want to implement standard looking pattern matching with guards that turns into these case expressions
-- (And (Variable p) (Or (Variable p') _)) | p == p' = Variable p
-- (And (Variable p) (Or _ (Variable p'))) | p == p' = Variable p
-- 
--
-- proofs are all generated to make the match 
-- the default cases are all pureVNode v
-- guards are turned into if else blocks
-- constructors of outputs are wrapped in VariantFs -- MakePure class?
-- 

class ( HasF And t
      , HasF Variable t
      , HasF Or t
      , ForAllIn Functor t
      , ForAllIn Foldable t
      , ForAllIn Traversable t
      , Follow (Locate And t) t ~ And
      , FromSides (Locate And t)
      , Follow (Locate Variable t) t ~ Variable
      , FromSides (Locate Variable t)
      , Follow (Locate Or t) t ~ Or 
      , FromSides (Locate Or t)
      ) => Absorption t where
    absorption ::  STRef s Bool
               -> VariantF t (Pure # Molecule (VariantF t))
               -> ST s (Pure # Molecule (VariantF t))

instance ( HasF And t
         , HasF Variable t
         , HasF Or t
         , ForAllIn Functor t
         , ForAllIn Foldable t
         , ForAllIn Traversable t
         , Follow (Locate And t) t ~ And
         , FromSides (Locate And t)
         , Follow (Locate Variable t) t ~ Variable
         , FromSides (Locate Variable t)
         , Follow (Locate Or t) t ~ Or 
         , FromSides (Locate Or t)
         ) => Absorption t where
    absorption changed v@(VariantF tag res) =
        case testEquality tag (fromSides @(Locate And t)) of
          Just Refl ->
            case res of
              And (Pure (Molecule l@(VariantF tagl resl))) (Pure (Molecule r@(VariantF tagr resr))) -> 
                case testEquality tagl (fromSides @(Locate Variable t)) of
                  Just Refl -> -- var /\ ?
                    case resl of
                      Variable p ->                       
                        case testEquality tagr (fromSides @(Locate Or t)) of
                          Just Refl -> -- var /\ (? \/ ?)
                            case resr of
                              Or (Pure (Molecule (VariantF tagrl resrl))) (Pure (Molecule (VariantF tagrr resrr))) ->                              
                                case testEquality tagrl (fromSides @(Locate Variable t)) of
                                  Just Refl -> -- var /\ (var \/ ?)
                                    case resrl of
                                      Variable p' -> if p == p'
                                                       then do
                                                         writeSTRef changed True
                                                         pure $ iVariable p
                                                       else pureVNode v
                                  Nothing -> 
                                    case testEquality tagrr (fromSides @(Locate Variable t)) of
                                      Just Refl -> -- var /\ (? \/ var) 
                                        case resrr of
                                          Variable p' -> if p == p'
                                                           then do
                                                             writeSTRef changed True
                                                             pure $ iVariable p
                                                           else pureVNode v
                                      Nothing -> pureVNode v
                          Nothing -> pureVNode v
                  Nothing ->
                    case testEquality tagr (fromSides @(Locate Variable t)) of
                      Just Refl -> 
                        case resr of
                          Variable p -> -- ? /\ var
                            case testEquality tagl (fromSides @(Locate Or t)) of
                              Just Refl -> -- (? \/ ?) /\ var
                                case resl of
                                  Or (Pure (Molecule (VariantF tagll resll))) (Pure (Molecule (VariantF taglr reslr))) ->                              
                                    case testEquality tagll (fromSides @(Locate Variable t)) of
                                      Just Refl -> -- (var \/ ?) /\ var 
                                        case resll of
                                          Variable p' -> if p == p'
                                                          then do
                                                            writeSTRef changed True
                                                            pure $ iVariable p
                                                          else pureVNode v
                                      Nothing -> 
                                        case testEquality taglr (fromSides @(Locate Variable t)) of
                                          Just Refl -> -- (? \/ var) /\ var 
                                            case reslr of
                                              Variable p' ->  if p == p'
                                                                then do
                                                                  writeSTRef changed True
                                                                  pure $ iVariable p
                                                                else pureVNode v 
                                          Nothing -> pureVNode v
                              Nothing -> pureVNode v
                      Nothing -> pure $ Pure $ Molecule (VariantF tag res) 
          Nothing ->
            case testEquality tag (fromSides @(Locate Or t)) of
              Just Refl ->
                case res of
                  Or (Pure (Molecule l@(VariantF tagl resl))) (Pure (Molecule r@(VariantF tagr resr))) -> 
                    case testEquality tagl (fromSides @(Locate Variable t)) of
                      Just Refl -> -- var \/ ?
                        case resl of
                          Variable p ->                       
                            case testEquality tagr (fromSides @(Locate And t)) of
                              Just Refl -> -- var \/ (? /\ ?)
                                case resr of
                                  And (Pure (Molecule (VariantF tagrl resrl))) (Pure (Molecule (VariantF tagrr resrr))) ->                              
                                    case testEquality tagrl (fromSides @(Locate Variable t)) of
                                      Just Refl -> -- var \/ (var /\ ?)
                                        case resrl of
                                          Variable p' -> if p == p'
                                                           then do
                                                             writeSTRef changed True
                                                             pure $ iVariable p
                                                           else pureVNode v
                                      Nothing -> 
                                        case testEquality tagrr (fromSides @(Locate Variable t)) of
                                          Just Refl -> -- var \/ (? /\ var) 
                                            case resrr of
                                              Variable p' -> if p == p'
                                                               then do
                                                                 writeSTRef changed True
                                                                 pure $ iVariable p
                                                               else pureVNode v
                                          Nothing -> pureVNode v
                              Nothing -> pureVNode v
                      Nothing ->
                        case testEquality tagr (fromSides @(Locate Variable t)) of
                          Just Refl -> 
                            case resr of
                              Variable p -> -- ? \/ var
                                case testEquality tagl (fromSides @(Locate And t)) of
                                  Just Refl -> -- (? /\?) \/ var
                                    case resl of
                                      And (Pure (Molecule (VariantF tagll resll))) (Pure (Molecule (VariantF taglr reslr))) -> 
                                        case testEquality tagll (fromSides @(Locate Variable t)) of
                                          Just Refl -> -- (var /\ ?) \/ var 
                                            case resll of
                                              Variable p' -> if p == p'
                                                              then do
                                                                writeSTRef changed True
                                                                pure $ iVariable p
                                                              else pureVNode v
                                          Nothing -> 
                                            case testEquality taglr (fromSides @(Locate Variable t)) of
                                              Just Refl -> -- (? /\ var) \/ var 
                                                case reslr of
                                                  Variable p' ->  if p == p'
                                                                    then do
                                                                      writeSTRef changed True
                                                                      pure $ iVariable p
                                                                    else pureVNode v 
                                              Nothing -> pureVNode v
                                  Nothing -> pureVNode v 
                          Nothing -> pure $ Pure $ Molecule (VariantF tag res) 
              Nothing -> pureVNode v 


