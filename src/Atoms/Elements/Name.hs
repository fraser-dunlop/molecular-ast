module Atoms.Elements.Name where
import Atoms.Molecule.Pretty
import GHC.Generics
import qualified Text.PrettyPrint as Pretty


data Name = Name String
   deriving stock Show
   deriving (Eq,Ord,Generic) 

instance Pretty Name where
   pPrintPrec _ _ (Name n) = Pretty.text n 

