{-# LANGUAGE FlexibleContexts, BlockArguments, OverloadedStrings #-}
{-# OPTIONS_GHC -fplugin=Type.Compare.Plugin -fconstraint-solver-iterations=1000 -freduction-depth=0 #-}
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.Except
import           Control.Monad.RWS
import           Control.Monad.ST
import qualified Data.Map as Map
import           Hyper
import           Hyper.Infer
import           Hyper.Unify
import           Hyper.Unify.Apply
import           Hyper.Unify.Generalize
import           Hyper.Unify.QuantifiedVar
import           Hyper.Recurse
import           Hyper.Type.AST.Nominal
import           Hyper.Type.AST.Scheme
--import           FOL 
import           System.Exit (exitFailure)
import qualified Text.PrettyPrint as Pretty
import           Text.PrettyPrint.HughesPJClass (Pretty(..))
--import           TypeLang

import           Prelude

import Type.Set
import Type.Set.Variant
import Type.Set.VariantF
import Atoms.Elements.Type
import Atoms.Elements.TypeBool
import Atoms.Elements.And
import Atoms.Elements.Or
import Atoms.Elements.Not
import Atoms.Elements.Variable
import Atoms.Elements.Implies
import Atoms.Elements.IfAndOnlyIf
import Atoms.Elements.Parens
import Atoms.Molecule.AST
import Atoms.Molecule.TypeError
import Atoms.Molecule.Parser
import Atoms.Molecule.Pretty
import Atoms.Molecule.Gen
import Atoms.Molecule.PureInfer
import Atoms.Molecule.HasInferredType
import Atoms.Molecule.HasTypeConstraints
import Atoms.Molecule.VarType


import Atoms.Molecule.Infer
import Atoms.Molecule.Infer1
import Atoms.Molecule.InferOf
import Atoms.Molecule.InferScope
import Atoms.Molecule.RTraversable
import Atoms.Molecule.RTraversableInferOf
import Atoms.Molecule.Types

import Atoms.Chemistry.Cascades.DeMorgan

import Atoms.Chemistry.Reductions.RemoveParens

import Atoms.Chemistry.Reductions.EliminateImplies
import Atoms.Chemistry.Reductions.EliminateIfAndOnlyIf
import Atoms.Chemistry.Transformations.DeMorgan
import Atoms.Chemistry.Transformations.DoubleNegation
import Atoms.Chemistry.Telescopes.Example
import Atoms.Chemistry.Dilution

import Data.Proxy


import Text.Megaparsec
import Data.Void
import Data.Text (Text, pack)


type SimpleMoleculeP = (Insert Parens
                       (Insert Implies
                       (Insert IfAndOnlyIf
                       (Insert And 
                       (Insert Or
                       (Insert Not
                       (Insert Variable ('Empty))))))))




type SimpleMolecule = (Insert Implies
                      (Insert IfAndOnlyIf
                      (Insert And 
                      (Insert Or
                      (Insert Not
                      (Insert Variable ('Empty)))))))

type SimplerMolecule = (Insert IfAndOnlyIf
                       (Insert And 
                       (Insert Or
                       (Insert Not
                       (Insert Variable ('Empty))))))


type SimplestMolecule = (Insert And 
                        (Insert Or
                        (Insert Not
                        (Insert Variable ('Empty)))))

type SimplestMoleculeTypeable =  (Insert Type (Insert TypeBool (Insert And 
                                 (Insert Or
                                 (Insert Not
                                 (Insert Variable ('Empty)))))))

inferSimple :: Pure # (Molecule (VariantF SimplestMoleculeTypeable))
       -> Either (TypeError SimplestMoleculeTypeable # Pure)
                 (Pure # Scheme (Types SimplestMoleculeTypeable) (TypeOf (Molecule (VariantF SimplestMoleculeTypeable)))) 
inferSimple = execPureInfer . inferExpr

parseSomeMol :: Text -> Either (ParseErrorBundle Text Void) ((Molecule (VariantF SimpleMoleculeP)) # Pure) 
parseSomeMol = runParser (parser LeftRecursive) "" 


genTest :: IO (Pure # (Molecule (VariantF SimpleMolecule)))
genTest = do
   gend <- genTimeLimited gen 1000 
   if length (Pretty.render (pPrint gend)) < 20
      then genTest
      else return gend

-- type parameter t lets us form a telescope of rewrites
reduction :: ( RemoveParens f t
             , DeMorgan t
             , EliminateImplies t q
             ) => Pure # (Molecule (VariantF f)) 
               -> (Bool, Pure # (Molecule (VariantF q)))
reduction molecule =
   let (c,p) = removeParens molecule
       ((c2,_),p2) = deMorganNegationOfDisjunctionFixed p 
       (c3,p3) = eliminateImplies p2
    in (c || c2 || c3, p3)



main :: IO ()
main = do
    void $ sequence $ replicate 10 $ do
        putStrLn "random generating"
        gend <- genTest     
        print $ pPrint gend
        putStrLn "parsing"
        case parseSomeMol $ pack $ Pretty.render $ pPrint gend of
             Left err -> error $ show err 
             Right q -> do
                -- TODO implement equality on Molecules
                -- p should equal gend since we parse Parens added by pretty printing then remove them 
                let (c,p) = removeParens (Pure q)  
                putStrLn $ "removeParens " ++ show c
                print $ pPrint p
                putStrLn "deMorganNegationOfConjunctionFixed"
                let p1 = deMorganNegationOfConjunctionFixed p 
                print $ fst p1
                print $ pPrint $ snd p1 
                putStrLn "deMorganNegationOfDisjunctionFixed"
                let p2 = deMorganNegationOfDisjunctionFixed $ snd p1 
                print $ fst p2
                print $ pPrint $ snd p2
                             

                let (c3,p3 :: Pure # Molecule (VariantF SimplerMolecule)) = eliminateImplies $ snd p2 
                putStrLn $ "eliminateImplies " ++ show c3
                print $ pPrint p3

                putStrLn "doubleNegation"
                let p4 = foldMolecule doubleNegation p3 
                print $ pPrint p4

                putStrLn "deMorganNegationOfConjunctionFixed"
                let p5 = deMorganNegationOfConjunctionFixed p4 
                print $ fst p5
                print $ pPrint $ snd p5
                putStrLn "deMorganNegationOfDisjunctionFixed"
                let p6 = deMorganNegationOfDisjunctionFixed $ snd p5
                print $ fst p6
                print $ pPrint $ snd p6

                putStrLn "doubleNegation"
                let p7 = foldMolecule doubleNegation $ snd p6 
                print $ pPrint p7

                let (ch, p8 :: Pure # Molecule (VariantF SimplerMolecule)) = reduction (Pure q) 
                putStrLn $ "reduction " ++ show ch
                print $ pPrint p8


                let (ch, p9 :: Pure # Molecule (VariantF SimplestMolecule)) = eliminateIfAndOnlyIf p8 
                putStrLn $ "exampleIfAndOnlyIf " ++ show ch
                print $ pPrint p9


                let (ch, p10 :: Pure # Molecule (VariantF SimplerMolecule)) = exampleTelescope (Pure q) 
                putStrLn $ "exampleTelescope " ++ show ch
                print $ pPrint p10


                let p11 :: Pure # Molecule (VariantF SimplestMoleculeTypeable) =
                         dilute (Proxy @Type) $ dilute (Proxy @TypeBool) p9

-- | type checks okay but crashes at runtime with
-- molecular-ast-test-exe: (^?!): empty Fold
-- CallStack (from HasCallStack):
--  error, called at src/Control/Lens/Fold.hs:1310:28 in lens-4.18.1-44tD1ZSGzOC7tE3w8F9M7F:Control.Lens.Fold
--  ^?!, called at src/Atoms/Molecule/VarType.hs:31:17 in molecular-ast-0.1.0.0-Es4X0GdIAVP4ZqpZAKnG0E:Atoms.Molecule.VarType
--                case inferSimple p11 of
--                    Left _ -> print "inference failed"
--                    Right _ -> print "inference succeeded"

            

                putStrLn ""


