{-# LANGUAGE FlexibleInstances    #-}
module Atoms.Chemistry.Telescopes.CNF.Checkable where
import Atoms.Chemistry.Reductions.CNF.Conjunctions
import Atoms.Chemistry.Reductions.CNF.Disjunctions
import Atoms.Chemistry.Reductions.CNF.Literals
import Atoms.Molecule.AST
import Hyper
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF

-- | When your molecule is already in CNF it can be transformed to a format where the type inference can confirm it is in CNF
class ( Literals m a b
      , Disjunctions b c
      , Conjunctions c d 
      ) => CheckableCNF m a b c d where
    transformToCheckableCNF :: Pure # (Molecule (VariantF a)) 
                            -> m (Bool, Pure # (Molecule (VariantF d)))

instance ( Literals m a b
         , Disjunctions b c
         , Conjunctions c d 
         ) => CheckableCNF m a b c d where 
    transformToCheckableCNF molecule = do
        (cb, b) <- literals molecule
        let (cc, c) = disjunctions b
            (cd, d) = conjunctions c
        pure (cb || cc || cd , d)


