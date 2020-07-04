{-# LANGUAGE QuasiQuotes          #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Chemistry.Transformations.PropCalc.Absorption_TH where
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

absorptionTH changed v@(And (Variable p) (Or (Variable p') _)) = 
    if p == p' 
      then do
        writeSTRef changed True
        pure (iVariable p) 
      else pureVNode v 
absorptionTH changed v@(And (Not (Variable p)) (Or (Not (Variable p')) _)) = 
    if p == p' 
      then do
        writeSTRef changed True
        pure (iNot (iVariable p)) 
      else pureVNode v 
absorptionTH changed v@(And (Variable p) (Or _ (Variable p'))) = 
    if p == p' 
      then do
        writeSTRef changed True
        pure (iVariable p) 
      else pureVNode v 
absorptionTH changed v@(And (Not (Variable p)) (Or _ (Not (Variable p')))) | p == p' = do 
    writeSTRef changed True
    pure (iNot (iVariable p)) 

|]
