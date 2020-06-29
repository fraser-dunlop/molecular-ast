{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Chemistry.Telescopes.Example where
import Atoms.Chemistry.Reductions.EliminateImplies
import Atoms.Chemistry.Reductions.EliminateIfAndOnlyIf
import Atoms.Chemistry.Reductions.RemoveParens
import Atoms.Molecule.AST
import Hyper
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF

class ( RemoveParens a b
      , EliminateImplies b c
      , EliminateIfAndOnlyIf c d 
      ) => ExampleTelescope a b c d where
    exampleTelescope :: Pure # (Molecule (VariantF a)) 
                     -> (Bool, Pure # (Molecule (VariantF d)))

instance forall a b c d .
         ( RemoveParens a b
         , EliminateImplies b c
         , EliminateIfAndOnlyIf c d 
         ) => ExampleTelescope a b c d where 
    exampleTelescope molecule =
        let (cb, b) = removeParens molecule
            (cc, c) = eliminateImplies b
            (cd, d) = eliminateIfAndOnlyIf c
         in (cb || cc || cd, d)


