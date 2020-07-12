{-# LANGUAGE QuasiQuotes          #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Chemistry.Transformations.PropCalc.Idempotency where
import Atoms.Chemistry.Utils.TH
import Atoms.Elements.Generic.Variable
import Atoms.Elements.PropCalc.And
import Atoms.Elements.PropCalc.Not
import Atoms.Elements.PropCalc.Or
import Atoms.Molecule.AST
import Data.Type.Equality
import Hyper
import Hyper.Type.Pure
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF
import Data.STRef
import Control.Monad.ST

[transformation|
-- p /\ p = p 
idempotency changed ((Variable a) `And` (Variable b)) | a == b =
  Just (iVariable a)
-- (x /\ p) /\ p = x /\ p
idempotency changed ((x `And` (Variable a)) `And` (Variable b)) | a == b =
  Just (x `iAnd` (iVariable a))
-- p \/ p = p 
idempotency changed ((Variable a) `Or` (Variable b)) | a == b =
  Just (iVariable a)
-- (x \/ p) \/ p = x \/ p
idempotency changed ((x `Or` (Variable a)) `Or` (Variable b)) | a == b =
  Just (x `iOr` (iVariable a))
-- !p /\ !p = !p 
idempotency changed ((Not (Variable a)) `And` (Not (Variable b))) | a == b =
  Just (iNot (iVariable a))
-- (x /\ !p) /\ !p = x /\ !p 
idempotency changed ((x `And` (Not (Variable a))) `And` (Not (Variable b))) | a == b =
  Just (x `iAnd` (iNot (iVariable a)))
-- !p \/ !p = !p 
idempotency changed ((Not (Variable a)) `Or` (Not(Variable b))) | a == b =
  Just (iNot (iVariable a))
-- (x \/ !p) \/ !p = x \/ !p 
idempotency changed ((x `Or` (Not (Variable a))) `Or` (Not(Variable b))) | a == b =
  Just (x `iOr` (iNot (iVariable a)))
|]
