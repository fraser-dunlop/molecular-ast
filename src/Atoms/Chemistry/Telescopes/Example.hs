{-# LANGUAGE FlexibleInstances    #-}
module Atoms.Chemistry.Telescopes.Example where
import Atoms.Chemistry.Cascades.DeMorgan
import Atoms.Chemistry.Cascades.DistributeOrsOverAnds
import Atoms.Chemistry.Cascades.DoubleNegation
import Atoms.Chemistry.Cascades.FOL.LitBoolElimination
import Atoms.Chemistry.Cascades.FOL.Tautology
import Atoms.Chemistry.Cascades.FOL.Contradiction
import Atoms.Chemistry.Cascades.FOL.NegateLitBool
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
      , DistributeOrsOverAndsCascades d
      , LitBoolEliminationCascades d
      , TautologyCascades d
      , ContradictionCascades d
      , NegateLitBoolCascades d
      ) => ExampleTelescope a b c d where
    exampleTelescope :: Pure # (Molecule (VariantF a)) 
                     -> (Bool, Pure # (Molecule (VariantF d)))

instance ( RemoveParens a b
         , EliminateImplies b c
         , EliminateIfAndOnlyIf c d 
         , DeMorganCascades d
         , DoubleNegationCascades d
         , DistributeOrsOverAndsCascades d
         , LitBoolEliminationCascades d
         , TautologyCascades d
         , ContradictionCascades d
         , NegateLitBoolCascades d
         ) => ExampleTelescope a b c d where 
    exampleTelescope molecule =
        let (cb, b) = removeParens molecule
            (cc, c) = eliminateImplies b
            (cd, d) = eliminateIfAndOnlyIf c
            e = fixedPointLoop [ litBoolEliminationFixed
                               , negateLitBoolFixed
                               , tautologyEliminationFixed
                               , contradictionEliminationFixed
                               , deMorganNegationOfDisjunctionFixed
                               , deMorganNegationOfConjunctionFixed
                               , doubleNegationFixed
                               , distributeOrsOverAndsFixed
                               ] d 
         in (cb || cc || cd , e)


