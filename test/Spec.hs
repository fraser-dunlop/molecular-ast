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
import Atoms.Molecule.AST
import Atoms.Molecule.TypeError
import Atoms.Molecule.Parser
import Atoms.Molecule.Pretty
import Atoms.Molecule.Gen
import Atoms.Molecule.PureInfer
import Atoms.Molecule.HasInferredType
import Atoms.Molecule.HasTypeConstraints

import Atoms.Molecule.Infer
import Atoms.Molecule.Infer1
import Atoms.Molecule.InferOf
import Atoms.Molecule.InferScope
import Atoms.Molecule.RTraversable
import Atoms.Molecule.RTraversableInferOf
import Atoms.Molecule.Types

import Atoms.Chemistry.Cascades.DeMorgan

import Atoms.Chemistry.Reductions.EliminateImplies
import Atoms.Chemistry.Transformations.DeMorgan
import Atoms.Chemistry.Transformations.DoubleNegation


import Text.Megaparsec
import Data.Void
import Data.Text (Text, pack)



type SimpleMolecule = (Insert Implies
                      (Insert And 
                      (Insert Or
                      (Insert Not
                      (Insert Variable ('Empty))))))

type SimplerMolecule = (Insert And 
                       (Insert Or
                       (Insert Not
                       (Insert Variable ('Empty)))))


parseSomeMol :: Text -> Either (ParseErrorBundle Text Void) ((Molecule (VariantF SimpleMolecule)) # Pure) 
parseSomeMol = runParser (parser LeftRecursive) "" 



testSomeMol :: Either (ParseErrorBundle Text Void) ((Molecule (VariantF SimpleMolecule)) # Pure) 
testSomeMol = runParser (parser LeftRecursive) "" "a -> b \\/ c" 

--shouldParseAs :: (Pure # (Molecule (VariantF SimpleMolecule))) 
--shouldParseAs = iVariable "a" `iImplies` (iVariable "b" `iOr` iVariable "c") 


--testSimpleMolecule :: Pure # (Molecule (VariantF SimpleMolecule)) 
--                   -> Either (Pure # TypeError SimpleMolecule) (Pure # (Molecule (VariantF SimpleMolecule)))

--testSimpleMolecule expr  = execPureInfer (inferExpr expr)


genTest :: IO (Pure # (Molecule (VariantF SimpleMolecule)))
genTest = do
   gend <- genTimeLimited gen 1000 
   if length (Pretty.render (pPrint gend)) < 20
      then genTest
      else return gend


main :: IO ()
main = do
    void $ sequence $ replicate 10 $ do
        putStrLn "random generating"
        gend <- genTest     
        print $ pPrint gend
        putStrLn "parsing"
        case parseSomeMol $ pack $ Pretty.render $ pPrint gend of
             Left err -> error $ show err 
             Right p -> do
 
                putStrLn "deMorganNegationOfConjunctionFixed"
                let p1 = deMorganNegationOfConjunctionFixed (Pure p)
                print $ fst p1
                print $ pPrint $ snd p1 
                putStrLn "deMorganNegationOfDisjunctionFixed"
                let p1 = deMorganNegationOfDisjunctionFixed (Pure p)
                print $ fst p1
                print $ pPrint $ snd p1 
               

              
                putStrLn "eliminateImplies"
                let p2 :: Pure # Molecule (VariantF SimplerMolecule) = foldMolecule eliminateImplies (Pure p)
                print $ pPrint p2

                putStrLn "doubleNegation"
                let p3 :: Pure # Molecule (VariantF SimpleMolecule) = foldMolecule doubleNegation (Pure p)
                print $ pPrint p3

                putStrLn ""


