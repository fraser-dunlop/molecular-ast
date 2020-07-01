{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Chemistry.Telescopes.CNF.Flatten where
import Atoms.Chemistry.Reductions.CNF.Flatten
import Atoms.Molecule.AST
import Hyper
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF

-- | When a molecule is in checkable CNF form it can be flattened to a single atom encoding a CNF 
class ( MoveLiteralsIntoFlatDisjunctions m f 
      , MoveDisjunctionsIntoFlatDisjunctions m f 
      , MoveFlatDisjunctionsIntoFlatConjunctions m f 
      , MoveConjunctionsIntoFlatConjunctions m f 
      ) => FlattenCNF m f where
    flattenCNF :: Pure # (Molecule (VariantF f)) 
               -> m (Bool, Pure # (Molecule (VariantF f)))

instance ( MoveLiteralsIntoFlatDisjunctions m f 
         , MoveDisjunctionsIntoFlatDisjunctions m f 
         , MoveFlatDisjunctionsIntoFlatConjunctions m f 
         , MoveConjunctionsIntoFlatConjunctions m f 
         ) => FlattenCNF m f where
    flattenCNF molecule = do
        (cb, b) <- moveLiteralsIntoFlatDisjunction molecule
        (cc, c) <- flattenDisjunctions b
        (cd, d) <- moveFlatDisjunctionsIntoFlatConjunction c
        (ce, e) <- flattenConjunctions d 
        pure (cb || cc || cd || ce, e)


