{-# LANGUAGE FlexibleInstances    #-}
module Atoms.Chemistry.Telescopes.Example where
import Atoms.Chemistry.Cascades.DeMorgan
import Atoms.Chemistry.Cascades.DoubleNegation
import Atoms.Chemistry.Reductions.EliminateImplies
import Atoms.Chemistry.Reductions.EliminateIfAndOnlyIf
import Atoms.Chemistry.Reductions.RemoveParens
import Atoms.Chemistry.Utils.FixedPoint
import Atoms.Molecule.AST
import Hyper
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF

class ( RemoveParens a b
      , EliminateImplies b c
      , EliminateIfAndOnlyIf c d 
      , DeMorganCascades d
      , DoubleNegationCascades d
      ) => ExampleTelescope a b c d where
    exampleTelescope :: Pure # (Molecule (VariantF a)) 
                     -> (Bool, Pure # (Molecule (VariantF d)))

instance ( RemoveParens a b
         , EliminateImplies b c
         , EliminateIfAndOnlyIf c d 
         , DeMorganCascades d
         , DoubleNegationCascades d
         ) => ExampleTelescope a b c d where 
    exampleTelescope molecule =
        let (cb, b) = removeParens molecule
            (cc, c) = eliminateImplies b
            (cd, d) = eliminateIfAndOnlyIf c
            e = fixedPointLoop [ deMorganNegationOfDisjunctionFixed
                               , deMorganNegationOfConjunctionFixed
                               , doubleNegationFixed
                               ] d 
         in (cb || cc || cd , e)


