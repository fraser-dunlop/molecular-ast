module Atoms.Chemistry.Solutions.CNF.MiniSat where
import Atoms.Elements.CNF.Flattened
import Atoms.Elements.CNF.Literal
import Atoms.Elements.Name
import Data.Map
import SAT.MiniSat

literal :: Literal h -> Formula Name 
literal (Positive nm) = Var nm
literal (Negative nm) = Not (Var nm)

disjunction :: FlatDisjunction h -> Formula Name 
disjunction (FlatDisjunctionSingleton s) = literal s
disjunction (FlatDisjunctionNode left right) = disjunction left :||: disjunction right

conjunction :: FlatConjunction h -> Formula Name 
conjunction (FlatConjunctionSingleton d) = disjunction d 
conjunction (FlatConjunctionNode left right) = conjunction left :&&: conjunction right 

solveFlatConjunction :: FlatConjunction h -> Maybe (Map Name Bool) 
solveFlatConjunction = solve . conjunction

