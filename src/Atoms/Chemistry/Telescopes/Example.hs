{-# LANGUAGE FlexibleInstances    #-}
module Atoms.Chemistry.Telescopes.Example where
import Atoms.Chemistry.Cascades.PropCalc.DeMorgan
import Atoms.Chemistry.Cascades.PropCalc.DistributeOrsOverAnds
import Atoms.Chemistry.Cascades.PropCalc.DoubleNegation
import Atoms.Chemistry.Cascades.PropCalc.DominationAndIdentity
import Atoms.Chemistry.Cascades.PropCalc.Tautology
import Atoms.Chemistry.Cascades.PropCalc.Contradiction
import Atoms.Chemistry.Cascades.PropCalc.NegateLitBool
import Atoms.Chemistry.Cascades.PropCalc.Idempotency
import Atoms.Chemistry.Cascades.PropCalc.Absorption
import Atoms.Chemistry.Cascades.PropCalc.ACSort
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
      , DominationAndIdentityCascades d
      , TautologyCascades d
      , ContradictionCascades d
      , NegateLitBoolCascades d
      , IdempotencyCascades d
      , AbsorptionCascades d
      , ACSortCascades d
      ) => ExampleTelescope a b c d where
    exampleTelescope :: Pure # (Molecule (VariantF a)) 
                     -> (Bool, Pure # (Molecule (VariantF d)))

instance ( RemoveParens a b
         , EliminateImplies b c
         , EliminateIfAndOnlyIf c d 
         , DeMorganCascades d
         , DoubleNegationCascades d
         , DistributeOrsOverAndsCascades d
         , DominationAndIdentityCascades d
         , TautologyCascades d
         , ContradictionCascades d
         , NegateLitBoolCascades d
         , IdempotencyCascades d
         , AbsorptionCascades d
         , ACSortCascades d
         ) => ExampleTelescope a b c d where 
    exampleTelescope molecule =
        let (cb, b) = removeParens molecule
            (cc, c) = eliminateImplies b
            (cd, d) = eliminateIfAndOnlyIf c
            e = fixedPointLoop [ aCSortFixed
                               , absorptionFixed
                               , dominationAndIdentityFixed
                               , negateLitBoolFixed
                               , tautologyFixed
                               , idempotencyFixed                               
                               , contradictionFixed
                               , doubleNegationFixed
                               , deMorganNegationOfDisjunctionFixed
                               , deMorganNegationOfConjunctionFixed
                               , distributeOrsOverAndsFixed
                               ] d 
         in (cb || cc || cd , e)


