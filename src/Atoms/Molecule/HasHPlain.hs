{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Molecule.HasHPlain where
import Atoms.Molecule.AST
import qualified Control.Lens as Lens
import Control.Lens.Operators
import Hyper
import Type.Set.VariantF

--makeHasHPlain [''Molecule]
--had to add Functor g by hand here - TODO find out if makeHasHPlain can add it for us 
--this is just the --ddump-splices output with Functor g added

instance (Functor g, Show (g (HPlain (Molecule g)))) =>
         HasHPlain (Molecule g) where
  data HPlain (Molecule g)
    = MoleculeP (g (HPlain (Molecule g)))
  hPlain
    = ((Lens.iso fromPlain) toPlain
         . Lens.from _Pure)
    where
        toPlain (Molecule x)
          = MoleculeP ((fmap (hPlain #)) x)
        fromPlain (MoleculeP x)
          = Molecule ((fmap (^. hPlain)) x)
deriving instance Eq (g (HPlain (Molecule g))) =>
                  Eq (HPlain (Molecule g))
deriving instance Ord (g (HPlain (Molecule g))) =>
                  Ord (HPlain (Molecule g))
deriving instance Show (g (HPlain (Molecule g))) =>
                  Show (HPlain (Molecule g))
