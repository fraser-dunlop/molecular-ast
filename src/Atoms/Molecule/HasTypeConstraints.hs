{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Molecule.HasTypeConstraints where
import Atoms.Molecule.InferScope
import Atoms.Molecule.AST
import Atoms.Molecule.ScopeTypes
import qualified Control.Lens as Lens
import Data.Map (Map)
import Hyper
import Hyper.Unify.Constraints
import Hyper.Infer
import Hyper.Type.AST.Nominal
import Type.Set.Variant
import Type.Set.VariantF


class HasTypeConstraints1 g f where
    verifyConstraints1 :: TypeConstraintsOf (Molecule (VariantF g))
                       -> f (h # (Molecule (VariantF g))) 
                       -> Maybe (f (WithConstraint h # (Molecule (VariantF g))))

instance ( ForAllIn (HasTypeConstraints1 g) g
         ) => HasTypeConstraints (Molecule (VariantF g)) where 
    type instance TypeConstraintsOf (Molecule (VariantF g)) = ScopeLevel
    verifyConstraints c (Molecule (VariantF ss v)) = 
       case forMember @_ @(HasTypeConstraints1 g) @g ss of
          Dict -> (Molecule . VariantF ss) <$> verifyConstraints1 c v  

