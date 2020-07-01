{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Molecule.ZipMatchable where 
import Atoms.Molecule.AST
import Generics.Constraints (makeDerivings)
import Control.Monad (join)
import Data.Type.Equality
import GHC.Generics
import Hyper
import Hyper.Class.ZipMatch
import Hyper.TH.Traversable
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF


class ZipMatchable1 g f where
   zipJoin1 :: f (p # (Molecule (VariantF g)))
            -> f (q # (Molecule (VariantF g)))
            -> Maybe (f ((p :*: q) # (Molecule (VariantF g))))


class ZipMatchable g where
   zipJoin :: VariantF g (p # (Molecule (VariantF g)))
           -> VariantF g (q # (Molecule (VariantF g)))
           -> Maybe (VariantF g ((p :*: q) # (Molecule (VariantF g))))

instance ( ForAllIn (ZipMatchable1 g) g
         ) => ZipMatchable g where
   zipJoin (VariantF ssl l) (VariantF ssr r) = do
      case testEquality ssl ssr of
         Just Refl ->
             case forMember @_ @(ZipMatchable1 g) @g ssl of
                Dict -> VariantF ssl <$> zipJoin1 l r 
         Nothing -> Nothing

instance ( ZipMatchable g
         ) => ZipMatch (Molecule (VariantF g)) where
    zipMatch (Molecule l) (Molecule r) = Molecule <$> (zipJoin l r)




