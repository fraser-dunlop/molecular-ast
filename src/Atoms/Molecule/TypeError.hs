{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Atoms.Molecule.TypeError where
import Atoms.Molecule.AST
import Atoms.Molecule.HasTypeConstraints
import Atoms.Molecule.Pretty
import Atoms.Elements.Name
import GHC.Generics
import Hyper
import Hyper.Unify.Error
import qualified Text.PrettyPrint as Pretty
import Type.Set.Variant
import Type.Set.VariantF


data TypeError g h
    = TypeError (UnifyError (Molecule (VariantF g)) h)
    | QVarNotInScope Name
    | VarNotInScope Name
    deriving Generic

instance (ForAllIn Pretty1 g) => Pretty (TypeError g # Pure) where
    pPrintPrec lvl p (TypeError e) = pPrintPrec lvl p e
    pPrintPrec _ _ (QVarNotInScope x) =
        Pretty.text "quantified type variable not in scope" <+> pPrint x
    pPrintPrec _ _ (VarNotInScope x) =
        Pretty.text "variable not in scope" <+> pPrint x
