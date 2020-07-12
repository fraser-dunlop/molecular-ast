{-# LANGUAGE QuasiQuotes          #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Chemistry.Transformations.PropCalc.Absorption where
import Atoms.Chemistry.Utils.TH
import Atoms.Elements.Generic.Variable
import Atoms.Elements.PropCalc.And
import Atoms.Elements.PropCalc.Or
import Atoms.Elements.PropCalc.Not
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
-- p /\ (p \/ _) --> p
absorption changed ((Variable p) `And` ((Variable p') `Or` _)) | (p == p') =
    Just (iVariable p) 
-- p /\ (_ \/ p) --> p
absorption changed ((Variable p) `And` (_ `Or` (Variable p'))) | p == p' =
    Just (iVariable p) 
-- (p \/ _) /\ p --> p
absorption changed (((Variable p') `Or` _) `And` (Variable p)) | p == p' = 
    Just (iVariable p) 
-- (_ \/ p) /\ p --> p
absorption changed ((_ `Or` (Variable p')) `And` (Variable q)) | q == p' = 
    Just (iVariable q) 
-- !p /\ (!p \/ _) --> !p
absorption changed ((Not (Variable p)) `And` ((Not (Variable p')) `Or` _)) | p == p' = 
    Just (iNot (iVariable p)) 
-- !p /\ (_ \/ !p) --> !p
absorption changed ((Not (Variable p)) `And` (_ `Or` (Not (Variable p')))) | p == p' = 
    Just (iNot (iVariable p)) 
-- (!p \/ _) /\ !p --> !p
absorption changed (((Not (Variable p')) `Or` _) `And` (Not (Variable p))) | p == p' = 
    Just (iNot (iVariable p)) 
-- (_ \/ !p) /\ !p --> !p
absorption changed ((_ `Or` (Not (Variable p'))) `And` (Not (Variable p))) | p == p' = 
    Just (iNot (iVariable p)) 
-- p \/ (p /\ _) --> p
absorption changed ((Variable p) `Or` ((Variable p') `And` _))  | p == p' = 
    Just (iVariable p) 
-- p \/ (_ /\ p) --> p
absorption changed ((Variable p) `Or` (_ `And` (Variable p'))) | p == p' = 
    Just (iVariable p) 
-- (p /\ _) \/ p --> p
absorption changed (((Variable p') `And` _) `Or` (Variable p)) | p == p' = 
    Just (iVariable p) 
-- (_ /\ p) \/ p --> p
absorption changed ((_ `And` (Variable p')) `Or` (Variable p)) | p == p' = 
    Just (iVariable p) 
-- !p \/ (!p /\ _) --> !p
absorption changed ((Not (Variable p)) `Or` ((Not (Variable p')) `And` _)) | p == p' = 
    Just (iNot (iVariable p)) 
-- !p \/ (_ /\ !p) --> !p
absorption changed ((Not (Variable p)) `Or` (_ `And` (Not (Variable p')))) | p == p' = 
    Just (iNot (iVariable p)) 
-- (!p /\ _) \/ !p --> !p
absorption changed (((Not (Variable p')) `And` _) `Or` (Not (Variable p))) | p == p' = 
    Just (iNot (iVariable p)) 
-- (_ /\ !p) \/ !p --> !p
absorption changed ((_ `And` (Not (Variable p'))) `Or` (Not (Variable p))) | p == p' = 
    Just (iNot (iVariable p)) 
|]
