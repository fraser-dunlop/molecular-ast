{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
module Atoms.Molecule.Class.VarType where
import Hyper
import Hyper.Infer
import Hyper.Unify

type family ScopeOf (t :: HyperType) :: HyperType

class HasScope m s where
    getScope :: m (s # UVarOf m)

class VarType m var expr where
    -- | Instantiate a type for a variable in a given scope
    varType ::
        ( UnifyGen m (TypeOf expr)
        , HasScope m (ScopeOf expr)) =>
        Proxy expr -> var -> ScopeOf expr # UVarOf m ->
        m (UVarOf m # TypeOf expr)

