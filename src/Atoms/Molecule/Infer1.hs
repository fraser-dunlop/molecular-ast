{-# LANGUAGE FlexibleContexts     #-}
module Atoms.Molecule.Infer1 where
import Atoms.Elements.Name
import Atoms.Molecule.AST
import Atoms.Molecule.InferOf
import Hyper
import Hyper.Infer
import Hyper.Unify
import Hyper.Unify.Generalize

class Infer1 m t g where
    liftInferBody :: ( MonadScopeLevel m
                     , LocalScopeType Name (UVarOf m # t) m
                     , LocalScopeType Name (GTerm (UVarOf m) # t) m
                     , UnifyGen m t
                     , Infer m t
                     )
                  => g (InferChild m h # t) 
                  -> m ((t # h), InferOf t # UVarOf m)


