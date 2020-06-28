module Atoms.Elements.Name where
import GHC.Generics

data Name = Name String
   deriving stock Show
   deriving (Eq,Ord,Generic) 

