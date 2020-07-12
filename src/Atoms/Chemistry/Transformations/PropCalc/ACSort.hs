{-# LANGUAGE QuasiQuotes          #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Chemistry.Transformations.PropCalc.ACSort where
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
aCSort changed ((Variable a) `And` (Variable b)) | b < a =
  Just ((iVariable b) `iAnd` (iVariable a))

aCSort changed ((Not (Variable a)) `And` (Variable b)) | b < a =
  Just ((iVariable b) `iAnd` (iNot (iVariable a)))

aCSort changed ((Variable a) `And` (Not (Variable b))) | b < a =
  Just ((iNot (iVariable b)) `iAnd` (iVariable a))

aCSort changed ((Not (Variable a)) `And` (Not (Variable b))) | b < a =
  Just ((iNot (iVariable b)) `iAnd` (iNot (iVariable a)))


aCSort changed ((Variable a) `Or` (Variable b)) | b < a =
  Just ((iVariable b) `iOr` (iVariable a))

aCSort changed ((Not (Variable a)) `Or` (Variable b)) | b < a =
  Just ((iVariable b) `iOr` (iNot (iVariable a)))

aCSort changed ((Variable a) `Or` (Not (Variable b))) | b < a =
  Just ((iNot (iVariable b)) `iOr` (iVariable a))

aCSort changed ((Not (Variable a)) `Or` (Not (Variable b))) | b < a =
  Just ((iNot (iVariable b)) `iOr` (iNot (iVariable a)))


aCSort changed ((x `And` (Variable a)) `And` (Variable b)) | b < a =
    Just ((x `iAnd` (iVariable b)) `iAnd` (iVariable a))

aCSort changed ((x `And` (Not (Variable a))) `And` (Variable b)) | b < a =
    Just ((x `iAnd` (iVariable b)) `iAnd` (iNot (iVariable a)))

aCSort changed ((x `And` (Variable a)) `And` (Not (Variable b))) | b < a =
    Just ((x `iAnd` (iNot (iVariable b))) `iAnd` (iVariable a))

aCSort changed ((x `And` (Not (Variable a))) `And` (Not (Variable b))) | b < a =
    Just ((x `iAnd` (iNot (iVariable b))) `iAnd` (iNot (iVariable a)))


aCSort changed (a `And` (b `And` c)) =
    Just ((a `iAnd` b) `iAnd` c)    

aCSort changed ((x `Or` (Variable a)) `Or` (Variable b)) | b < a =
    Just ((x `iOr` (iVariable b)) `iOr` (iVariable a))

aCSort changed ((x `Or` (Not (Variable a))) `Or` (Variable b)) | b < a =
    Just ((x `iOr` (iVariable b)) `iOr` (iNot (iVariable a)))

aCSort changed ((x `Or` (Variable a)) `Or` (Not (Variable b))) | b < a =
    Just ((x `iOr` (iNot (iVariable b))) `iOr` (iVariable a))

aCSort changed ((x `Or` (Not (Variable a))) `Or` (Not (Variable b))) | b < a =
    Just ((x `iOr` (iNot (iVariable b))) `iOr` (iNot (iVariable a)))


aCSort changed (a `Or` (b `Or` c)) =
    Just ((a `iOr` b) `iOr` c)    


aCSort changed ((a `Or` b) `Or` (c `Or` d)) =
    Just (((a `iOr` b) `iOr` c) `iOr` d)

aCSort changed ((a `And` b) `And` (c `And` d)) =
    Just (((a `iAnd` b) `iAnd` c) `iAnd` d)

|]