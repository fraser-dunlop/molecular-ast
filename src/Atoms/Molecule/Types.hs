{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Molecule.Types where
import Atoms.Molecule.AST
import qualified Control.Lens as Lens
import Generics.Constraints (makeDerivings, Constraints)
import Hyper
import Hyper.Class.Has
import Hyper.Type.AST.Nominal 
import Text.PrettyPrint.HughesPJClass (Pretty(..))
import Type.Set.VariantF


data Types g h = Types {
    _tTyp :: h :# (Molecule (VariantF g))
  } deriving Generic

Lens.makeLenses ''Types
makeZipMatch ''Types
makeHTraversableApplyAndBases ''Types
makeDerivings [''Eq, ''Ord, ''Show] [''Types]

--type instance NomVarTypes (Molecule (VariantF g)) = Types g 

instance Constraints (Types g h) Pretty => Pretty (Types g h) where
    pPrintPrec lvl p (Types typ ) =
        pPrintPrec lvl p typ

instance HasChild (Types g) (Molecule (VariantF g)) where getChild = tTyp

