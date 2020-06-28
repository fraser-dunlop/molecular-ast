{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE InstanceSigs           #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE QuantifiedConstraints  #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE RoleAnnotations        #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# OPTIONS_GHC -Wall               #-}

module Type.Set.VariantF
  ( -- * Core types
    VariantF (..)
  , HasF (..)

    -- * Decomposition proofs
  , decompRootF
  , SplitF (..)


    -- * Quantification
  , QuantifyOver(..)
  , ASum1(..)
  , ASumPrec1(..)
  , ASumPrecLR(..)
  , Gen(..)
  , Gen1(..)

    -- * Weakening
  , weakenF
  ) where

import Data.Type.Equality
import Type.Set.Variant
import Data.Functor.Classes
import Data.Constraint
import Type.Reflection
import Type.Set
import Control.Applicative
import Data.List (sortBy)
import Control.Monad (join)

------------------------------------------------------------------------------
--instance Choice1 RVar Not where
--  
-- | A 'VariantF' is a higher-order version of 'Variant' which can contain
--   any of the 'Functor's within its 'TypeSet'. You can use 'toVariantF' to
--   construct one, and 'fromVariantF' to pattern match it out.
data VariantF (bst :: TypeSet (k -> *)) (a :: k) where
  VariantF :: SSide ss -> Follow ss bst a -> VariantF bst a
type role VariantF nominal nominal

------------------------------------------------------------------------------
-- | A proof that the set @bst@ contains @f :: @.
class HasF (f :: k -> *) (bst :: TypeSet (k -> *)) where

  -- | Inject a @t@ into a 'VariantF'.
  toVariantF :: f a -> VariantF bst a

  -- | Attempt to project a 'VariantF' into @f a@. This might fail, because there
  -- is no guarantee that the 'VariantF' /actually contains/ @f a@.
  fromVariantF :: VariantF bst a -> Maybe (f a)

instance ( Follow (Locate f bst) bst ~ f
         , FromSides (Locate f bst)
         , Typeable (Locate f bst)
         ) => HasF f bst where
  toVariantF = VariantF (fromSides @(Locate f bst))
  fromVariantF (VariantF tag res) =
    case testEquality tag (fromSides @(Locate f bst)) of
      Just Refl -> Just res
      Nothing -> Nothing


------------------------------------------------------------------------------
-- | For Quantifying over ForAllIn Dicts in a VariantF.
-- Allows you to use forMember on every arm of the VariantF and collect a list.

data SomeSSide where
  SomeSSide :: SSide ss -> SomeSSide

goRight :: SomeSSide -> SomeSSide
goRight (SomeSSide ss) = SomeSSide (SR ss)

goLeft :: SomeSSide -> SomeSSide
goLeft (SomeSSide ss) = SomeSSide (SL ss)

-- QuantifyOver gets you a list of SomeSSide
class QuantifyOver (bst :: TypeSet (k -> *)) where
  forMembers :: [SomeSSide] 

instance () => QuantifyOver 'Empty where
  forMembers = [] 

instance (QuantifyOver l, QuantifyOver r
         ) => QuantifyOver ('Branch (a :: (k -> *))
                                     (l :: TypeSet (k -> *))
                                     (r :: TypeSet (k -> *))) where
  forMembers = (SomeSSide SNil):((goLeft <$> (forMembers @_ @l))
                             ++ (goRight <$> (forMembers @_ @r)))
 
------------------------------------------------------------------------------
-- | This idiom is useful for higher order parsing 
-- If each component of VariantF implements ASum1 they can run in parallel
-- and the first success is lifted to VariantF.
class ASum1 g f where
  liftASum :: (Alternative g) => g a -> g (f a)

instance ( QuantifyOver bst
         , ForAllIn (ASum1 g) bst
         ) => ASum1 g (VariantF bst) where
  liftASum p = foldr (<|>) empty ( (\(SomeSSide s) -> 
                                   case forMember @_ @(ASum1 g) @bst s of
                                        Dict -> VariantF s <$> liftASum p) <$> forMembers @_ @bst)

-- When parsing elements may require precedence
-- ASumPrec1 works just like ASumPrec but the highest tagged success succeeds first
class ASumPrec1 g f where
  liftASumPrec :: (Alternative g) => g a -> (Int, g (f a)) 

(<||>) :: Alternative g => (Int, g a) -> (Int, g a) -> (Int, g a)
(<||>) (_,l) (_,r) = (0, l <|> r)

instance ( QuantifyOver bst
         , ForAllIn (ASumPrec1 g) bst
         ) => ASumPrec1 g (VariantF bst) where
  liftASumPrec p = foldr (<||>) (0, empty)
                         (sortBy (\a b -> fst b `compare` fst a)
                              ((\(SomeSSide s) -> 
                                 case forMember @_ @(ASumPrec1 g) @bst s of
                                      Dict -> (VariantF s <$> ) <$> liftASumPrec p) <$> forMembers @_ @bst ))

-- | For left recursive grammars we might want a parser to fail because it is left recursive
-- e.g. parsing an infix binary operator we may want to say for the left argument
--       - parse me something that is not left recursive please!
--          - since otherwise the parser would spiral into an infinite recursion of doom
--
-- the d parameter lets you discriminate over classes of parsers in a granular way
-- data Discriminator = LeftRecursive | NotLeftRecursive
-- or something more exotic
class ASumPrecLR d g f where
  liftASumPrecLR :: (Alternative g) => d -> (d -> g a) -> (Int, g (f a))

instance ( QuantifyOver bst
         , ForAllIn (ASumPrecLR d g) bst
         ) => ASumPrecLR d g (VariantF bst) where
  liftASumPrecLR rec p =
       foldr (<||>) (0, empty)
           (sortBy (\a b -> fst b `compare` fst a)
                    ((\(SomeSSide s) -> 
                        case forMember @_ @(ASumPrecLR d g) @bst s of
                            Dict -> (VariantF s <$> ) <$> liftASumPrecLR rec p)
                               <$> forMembers @_ @bst ))



------------------------------------------------------------------------------
-- | This is for writing random generators!

class Gen g a where
  gen :: g a

class Gen1 g f where
  liftGen :: (Gen g a) => (forall x . [x] -> g x) -> g (f a)


instance ( Monad m
         , QuantifyOver bst
         , ForAllIn (Gen1 m) bst
         ) => Gen1 m (VariantF bst) where
  liftGen c = do
     let options = ((\(SomeSSide s) ->
              case forMember @_ @(Gen1 m) @bst s of
                  Dict -> VariantF s <$> liftGen c) <$> forMembers @_ @bst)
      in join (c options) 

------------------------------------------------------------------------------
-- | TODO
data SplitF f lbst rbst a
  = RootF (f a)
  | LSplitF (VariantF lbst a)
  | RSplitF (VariantF rbst a)

------------------------------------------------------------------------------
-- | TODO
decompRootF :: VariantF ('Branch f lbst rbst) a -> SplitF f lbst rbst a
decompRootF (VariantF SNil   t) = RootF t
decompRootF (VariantF (SL s) t) = LSplitF (VariantF s t)
decompRootF (VariantF (SR s) t) = RSplitF (VariantF s t)

------------------------------------------------------------------------------
-- | Weaken a 'VariantF' so that it can contain something else.
weakenF :: forall f bst a. VariantF bst a -> VariantF (Insert f bst) a
weakenF (VariantF (tag :: SSide ss) res)
  = VariantF (tag :: SSide ss) $
    case proveFollowInsert @ss @f @bst of
      HRefl -> res :: Follow ss bst a

instance (ForAllIn Functor bst) => Functor (VariantF bst) where
  fmap f (VariantF s r)
    = case forMember @_ @Functor @bst s of
      Dict -> VariantF s $ fmap f r

instance ( ForAllIn Functor bst
         , ForAllIn Foldable bst
         ) => Foldable (VariantF bst) where
  foldMap f (VariantF s r)
    = case forMember @_ @Foldable @bst s of
        Dict -> foldMap f r

instance ( ForAllIn Functor bst
         , ForAllIn Foldable bst
         , ForAllIn Traversable bst
         ) => Traversable (VariantF bst) where
  traverse f (VariantF s r)
    = case forMember @_ @Traversable @bst s of
        Dict -> VariantF s <$> traverse f r

instance ( ForAllIn Eq1 bst
         , ForAllIn Typeable bst
         ) => Eq1 (VariantF bst) where
  liftEq eq (VariantF (s :: SSide ss) r) (VariantF (s':: SSide ss') r')
    = case forMember @_ @Typeable @bst s of
      Dict -> case forMember @_ @Typeable @bst s' of
        Dict -> case eqTypeRep (typeRep @(Follow ss bst)) (typeRep @(Follow ss' bst)) of
          Nothing -> False
          Just HRefl -> case forMember @_ @Eq1 @bst s of
            Dict -> liftEq eq r r'

instance ( ForAllIn Eq1 bst
         , ForAllIn Typeable bst
         , Eq a
         ) => Eq (VariantF bst a) where
  (==) = eq1

instance ( ForAllIn Eq1 bst
         , ForAllIn Ord1 bst
         , ForAllIn Typeable bst
         ) => Ord1 (VariantF bst) where
  liftCompare cmp (VariantF (s :: SSide ss) r) (VariantF (s':: SSide ss') r')
    = case forMember @_ @Typeable @bst s of
      Dict -> case forMember @_ @Typeable @bst s' of
        Dict -> case eqTypeRep (typeRep @(Follow ss bst)) (typeRep @(Follow ss' bst)) of
          Nothing -> compare (toSideList s) (toSideList s')
          Just HRefl -> case forMember @_ @Ord1 @bst s of
            Dict -> liftCompare cmp r r'


instance ( ForAllIn Eq1 bst
         , ForAllIn Ord1 bst
         , ForAllIn Typeable bst
         , Ord a
         ) => Ord (VariantF bst a) where
  compare = compare1

instance ( ForAllIn Show1 bst
         ) => Show1 (VariantF bst) where

  liftShowsPrec :: forall a. (Int -> a -> ShowS)
    -> ([a] -> ShowS) -> Int -> VariantF bst a -> ShowS
  liftShowsPrec prec lPrec d (VariantF s r)
    = case forMember @_  @Show1 @bst s of
      Dict -> showParen (d > 5) $
        (showString "toVariantF " :: ShowS) .
        showString " $ " .
        liftShowsPrec prec lPrec (d+1) r

instance ( ForAllIn Show1 bst
         , Show a) => Show (VariantF bst a) where
  showsPrec = showsPrec1
