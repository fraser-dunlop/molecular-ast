{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
module Atoms.Molecule.VarType where
import Atoms.Elements.Name
import Atoms.Molecule.AST
import Atoms.Molecule.ScopeTypes
import Atoms.Molecule.HasInferredType
import qualified Control.Lens as Lens
import Control.Lens.Operators
import Data.Map (Map)
import Hyper
import Hyper.Class.Infer.InferOf
import Hyper.Unify
import Hyper.Type.AST.Var
import Hyper.Unify.Generalize
import Type.Set.VariantF




instance VarType Name (Molecule (VariantF g)) where
    varType _ h (ScopeTypes t) =
        r t
        where
            r ::
                forall m. UnifyGen m (Molecule (VariantF g)) =>
                Map Name (HFlip GTerm (Molecule (VariantF g)) # UVarOf m) ->
                m (UVarOf m # (Molecule (VariantF g)))
            r x =
                withDict (unifyRecursive (Proxy @m) (Proxy @(Molecule (VariantF g)))) $
                x ^?! Lens.ix h . _HFlip & instantiate


