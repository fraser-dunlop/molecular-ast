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

import Atoms.Reductions.EliminateImplies
import Atoms.Transformations.DeMorgan


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

foldMolecule :: (ForAllIn Functor f) => ((VariantF f) a -> a) -> Pure # (Molecule (VariantF f)) -> a
foldMolecule f (Pure (Molecule t)) = f (fmap (foldMolecule f) t)

genTest :: IO (Pure # (Molecule (VariantF SimpleMolecule)))
genTest = genTimeLimited gen 1 


main :: IO ()
main = do
    void $ sequence $ replicate 100 $ do
        putStrLn "random generating"
        gend <- genTest     
        print $ pPrint gend
        putStrLn "parsing"
        case parseSomeMol $ pack $ Pretty.render $ pPrint gend of
             Left err -> error $ show err 
             Right p -> do
                print $ pPrint p  
                putStrLn "deMorganNegationOfDisjunction"
                print $ pPrint $ foldMolecule deMorganNegationOfDisjunction (Pure p)
                
                -- | is this causing type checking to diverge?
                putStrLn "eliminateImplies"
                let el :: Pure # Molecule (VariantF SimplerMolecule) = foldMolecule eliminateImplies (Pure p)
                print $ pPrint el 
                putStrLn ""


