{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Molecule.ScopeTypes where
import Atoms.Molecule.AST
import Atoms.Elements.Name
import qualified Control.Lens as Lens
import Data.Map (Map)
import Generics.Constraints (makeDerivings)
import Hyper
import Hyper.Unify.Generalize
--import Hyper.Type.AST.Var
import Atoms.Molecule.Class.VarType

import Type.Set.VariantF

newtype ScopeTypes g v = ScopeTypes (Map Name (HFlip GTerm (Molecule (VariantF g)) v))
    deriving stock Generic
    deriving newtype (Semigroup, Monoid)

makeDerivings [''Show] [''ScopeTypes]
makeHTraversableAndBases ''ScopeTypes

Lens.makePrisms ''ScopeTypes

type instance ScopeOf (Molecule (VariantF g)) = ScopeTypes g 

