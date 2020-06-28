{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Atoms.Molecule.Pretty 
  ( module Atoms.Molecule.Pretty
  , module Text.PrettyPrint
  , module Text.PrettyPrint.HughesPJClass
  ) where
import Atoms.Molecule.AST
import Hyper
import Text.PrettyPrint ((<+>),Doc)
import Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens,PrettyLevel(..))
import Type.Set.Variant
import Type.Set.VariantF


-- Lifting Pretty to the (* -> *) level.
class Pretty1 f where
    liftPrintPrec :: (PrettyLevel -> Rational -> a -> Doc)
                  -> ([a] -> Doc)
                  -> PrettyLevel
                  -> Rational
                  -> f a
                  -> Doc 

-- When all of the components of (VariantF bst) are Pretty1 we can match out the instance
-- for the component. 
instance ( ForAllIn Pretty1 bst 
         ) => Pretty1 (VariantF bst) where
     liftPrintPrec prec lPrec (PrettyLevel lvl) p (VariantF s r) = 
         case forMember @_ @Pretty1 @bst s of
             Dict -> liftPrintPrec prec lPrec (PrettyLevel (lvl + 1)) p r

-- This allows for a generic Pretty instance for a Molecule.
instance (ForAllIn Pretty1 g) => Pretty (Molecule (VariantF g) # Pure) where
    pPrintPrec lvl p (Molecule x) = liftPrintPrec pPrintPrec (pPrintList lvl) lvl p x 


