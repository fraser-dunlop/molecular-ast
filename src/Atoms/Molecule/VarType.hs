{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Molecule.VarType where
import Atoms.Elements.Name
import Atoms.Molecule.AST
import Atoms.Molecule.ScopeTypes
import Atoms.Molecule.TypeError
import Atoms.Molecule.HasInferredType
import qualified Control.Lens as Lens
import Control.Lens.Operators
import Control.Monad.Except
import Data.Map (Map)
import Hyper
import Hyper.Class.Infer.InferOf
import Hyper.Unify
--import Hyper.Type.AST.Var
import Atoms.Molecule.Class.VarType
import Hyper.Unify.Generalize
import Type.Set.VariantF



instance forall m g h . (MonadError (TypeError g h) m) => VarType m  Name (Molecule (VariantF g)) where
    varType _ h (ScopeTypes t) =
        r t
        where
            r ::
                forall m g h. (MonadError (TypeError g h) m, UnifyGen m (Molecule (VariantF g))) =>
                Map Name (HFlip GTerm (Molecule (VariantF g)) # UVarOf m) ->
                m (UVarOf m # (Molecule (VariantF g)))
            r x =
                withDict (unifyRecursive (Proxy @m) (Proxy @(Molecule (VariantF g)))) $
                x ^? Lens.ix h . _HFlip & maybe (throwError (VarNotInScope h)) instantiate 


