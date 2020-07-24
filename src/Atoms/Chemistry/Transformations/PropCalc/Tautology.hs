{-# LANGUAGE QuasiQuotes          #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Chemistry.Transformations.PropCalc.Tautology where
import Atoms.Chemistry.Utils.TH
import Atoms.Elements.PropCalc.LitBool
import Atoms.Elements.PropCalc.Not
import Atoms.Elements.PropCalc.Or
import Atoms.Elements.Generic.Variable
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
-- p \/ !p = True
tautology ((Not (Variable a)) `Or` (Variable b)) | a == b =
  Just (Pure (Molecule (toVariantF (LitBool True))))
-- !p \/ p = True 
tautology ((Variable a) `Or` (Not (Variable b))) | a == b =
  Just (iLitBool True)
-- (x \/ !p) \/ p = True
tautology ((x `Or` (Variable a)) `Or` (Not (Variable b))) | a == b =
  Just (iLitBool True)
-- (x \/ p) \/ !p = True
tautology ((x `Or` (Not (Variable a))) `Or` (Variable b)) | a == b =
  Just (iLitBool True)
|]

