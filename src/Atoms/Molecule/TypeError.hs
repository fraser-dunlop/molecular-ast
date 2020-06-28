module Atoms.Molecule.TypeError where
import Atoms.Molecule.AST
import Atoms.Elements.Name
import GHC.Generics
import Hyper.Unify.Error
import Type.Set.VariantF

data TypeError g h
    = TypError (UnifyError (Molecule (VariantF g)) h)
    | QVarNotInScope Name
    deriving Generic
