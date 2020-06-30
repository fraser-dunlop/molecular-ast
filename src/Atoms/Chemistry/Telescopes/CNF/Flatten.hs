{-# LANGUAGE FlexibleInstances    #-}
module Atoms.Chemistry.Telescopes.CNF.Flatten where
import Atoms.Chemistry.Reductions.CNF.Flatten
import Atoms.Molecule.AST
import Hyper
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF

-- | When a molecule is in checkable CNF form it can be flattened to a single atom encoding a CNF 
class ( MoveLiteralsIntoFlatDisjunctions m a b 
      , MoveDisjunctionsIntoFlatDisjunctions m b c
      , MoveFlatDisjunctionsIntoFlatConjunctions m c d 
      , MoveConjunctionsIntoFlatConjunctions m d e
      ) => FlattenCNF m a b c d e where
    flattenCNF :: Pure # (Molecule (VariantF a)) 
               -> m (Bool, Pure # (Molecule (VariantF e)))

instance ( MoveLiteralsIntoFlatDisjunctions m a b 
         , MoveDisjunctionsIntoFlatDisjunctions m b c
         , MoveFlatDisjunctionsIntoFlatConjunctions m c d 
         , MoveConjunctionsIntoFlatConjunctions m d e
         ) => FlattenCNF m a b c d e where
    flattenCNF molecule = do
        (cb, b) <- moveLiteralsIntoFlatDisjunction molecule
        (cc, c) <- flattenDisjunctions b
        (cd, d) <- moveFlatDisjunctionsIntoFlatConjunction c
        (ce, e) <- flattenConjunctions d 
        pure (cb || cc || cd || ce, e)


