{-# LANGUAGE QuasiQuotes          #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Chemistry.Transformations.PropCalc.Contradiction where
import Atoms.Chemistry.Utils.TH
import Atoms.Elements.PropCalc.LitBool
import Atoms.Elements.PropCalc.Not
import Atoms.Elements.PropCalc.And
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
-- p /\ !p = False 
contradiction changed ((Variable a) `And` (Not (Variable b))) | a == b =
    Just (Pure (Molecule (toVariantF (LitBool False))))
-- !p /\ p = False 
contradiction changed ((Not (Variable a)) `And` (Variable b)) | a == b =
    Just (Pure (Molecule (toVariantF (LitBool False))))
-- (x /\ p) /\ !p = False 
contradiction changed ((x `And` (Variable a)) `And` (Not (Variable b))) | a == b =
    Just (Pure (Molecule (toVariantF (LitBool False))))
-- (x /\ !p) /\ p = False 
contradiction changed ((x `And` (Not (Variable a))) `And` (Variable b)) | a == b =
    Just (Pure (Molecule (toVariantF (LitBool False))))
|]
