{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Molecule.InferScope where
import Atoms.Elements.Name
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

data InferScope g v = InferScope
    { _varSchemes :: ScopeTypes g # v
    , _scopeLevel :: ScopeLevel

-- don't think this is needed since no nominal records
--    , _nominals :: Map Name (LoadedNominalDecl (Molecule (VariantF g)) # v)
    }

Lens.makeLenses ''InferScope
Lens.makePrisms ''InferScope

emptyInferScope :: InferScope g v
emptyInferScope = InferScope mempty (ScopeLevel 0) --mempty

