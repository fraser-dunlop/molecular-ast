{-# LANGUAGE FlexibleContexts     #-}
--{-# LANGUAGE FlexibleInstances    #-}

{-# LANGUAGE TemplateHaskell      #-}
module Atoms.Molecule.PureInferState where
import Atoms.Molecule.AST
import Atoms.Molecule.Types
import qualified Control.Lens as Lens
import Hyper
import Hyper.Unify.Binding
import Type.Set.Variant
import Type.Set.VariantF

data PureInferState g = PureInferState
    { _pisBindings :: Types g # Binding
    , _pisFreshQVars :: Types g # Const Int
    }

Lens.makeLenses ''PureInferState

emptyPureInferState :: PureInferState g
emptyPureInferState =
    PureInferState
    { _pisBindings = Types emptyBinding
    , _pisFreshQVars = Types (Const 0) 
    }

