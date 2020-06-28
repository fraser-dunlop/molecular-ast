{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Molecule.Infer where
import Atoms.Elements.Name
import Atoms.Molecule.AST
import Atoms.Molecule.ScopeTypes
import Atoms.Molecule.Infer1
import Atoms.Molecule.InferOf
import Hyper
import Hyper.Infer
import Hyper.Type.AST.Var
import Hyper.Unify
import Hyper.Unify.Generalize
import Data.Constraint
import Type.Set.Variant
import Type.Set.VariantF

-- When all the Atoms of a Molecule implement Infer1 we can infer for a Molecule.

instance
    ( ForAllIn Functor g 
    , ForAllIn (Infer1 m (Molecule (VariantF g))) g
    , MonadScopeLevel m
    , LocalScopeType Name (UVarOf m # (Molecule (VariantF g))) m
    , LocalScopeType Name (GTerm (UVarOf m) # (Molecule (VariantF g))) m
    , UnifyGen m (Molecule (VariantF g))
    , HasScope m (ScopeTypes g)
    ) =>
    Infer m (Molecule (VariantF g)) where
  inferBody (Molecule (VariantF ss r)) = case forMember @_ @(Infer1 m (Molecule (VariantF g))) @g ss of
                                         Dict -> liftInferBody r


