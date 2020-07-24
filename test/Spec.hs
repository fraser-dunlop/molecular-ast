{-# LANGUAGE FlexibleContexts, BlockArguments, OverloadedStrings #-}
{-# OPTIONS_GHC -fplugin=Type.Compare.Plugin -fconstraint-solver-iterations=1000 -freduction-depth=10000 #-}
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.Except
import           Control.Monad.RWS

import qualified Data.Map as Map
import           Hyper
import           Hyper.Infer
import           Hyper.Unify

import           Hyper.Unify.Generalize



import           Hyper.Type.AST.Scheme
--import           PropCalc 

import qualified Text.PrettyPrint as Pretty

--import           TypeLang

import           Prelude

import Type.Set

import Type.Set.VariantF
import Atoms.Elements.Generic.Type
import Atoms.Elements.PropCalc.TypeBool
import Atoms.Elements.PropCalc.LitBool
import Atoms.Elements.PropCalc.And
import Atoms.Elements.PropCalc.Or
import Atoms.Elements.PropCalc.Not
import Atoms.Elements.Generic.Variable
import Atoms.Elements.PropCalc.Implies
import Atoms.Elements.PropCalc.IfAndOnlyIf
import Atoms.Elements.Generic.Parens
import Atoms.Elements.Name
import Atoms.Molecule.AST
import Atoms.Molecule.TypeError
import Atoms.Molecule.Parser
import Atoms.Molecule.Pretty
import Atoms.Molecule.Gen
import Atoms.Molecule.PureInfer
import Atoms.Molecule.HasInferredType()
import Atoms.Molecule.HasTypeConstraints()
import Atoms.Molecule.VarType()


import Atoms.Molecule.Infer()
import Atoms.Molecule.Infer1()
import Atoms.Molecule.InferOf()
import Atoms.Molecule.InferScope
import Atoms.Molecule.RTraversable()
import Atoms.Molecule.RTraversableInferOf()
import Atoms.Molecule.Types
import Atoms.Molecule.ScopeTypes





import Atoms.Chemistry.Telescopes.Example
import Atoms.Chemistry.Dilution


import Atoms.Chemistry.Solutions.CNF.MiniSat (solveFlatConjunction)


import Atoms.Elements.CNF.TypeDisjunction
import Atoms.Elements.CNF.TypeConjunction
import Atoms.Elements.CNF.TypeLiteral
import Atoms.Elements.CNF.Literal
import Atoms.Elements.CNF.Disjunction
import Atoms.Elements.CNF.Conjunction
import Atoms.Elements.CNF.Flattened

import Atoms.Chemistry.Telescopes.PropCalcToCNF.Checkable
import Atoms.Chemistry.Telescopes.CNF.Flatten
import Atoms.Chemistry.Extractions.CNF.Flattened



import Data.Proxy()

import Hyper.Unify.New()
import Hyper.Unify.Generalize()

import qualified Data.Map as Map()

import Text.Megaparsec()
import Data.Void
import Data.Text (Text, pack)

import System.IO (hFlush, stdout)

import Test.Atoms.Chemistry.Transformations.Absorption

type SimpleMoleculeP = (Insert Parens SimpleMolecule)


type SimpleMoleculeGen = (Insert Implies 
                         (Insert IfAndOnlyIf
                         (Insert Variable 
                         (Insert Not
                         (Insert Or 
                         (Insert And 'Empty))))))


type SimpleMolecule = (Insert Implies SimplerMolecule)

type SimplerMolecule = (Insert IfAndOnlyIf SimplestMolecule) 


type SimplestMolecule =
                        (Insert Not
                        (Insert Or 
                        (Insert And (CNFCore))))




type CNFCore = (Insert Type
               (Insert TypeLiteral  
               (Insert TypeDisjunction
               (Insert TypeConjunction
               (Insert Conjunction 
               (Insert Disjunction
               (Insert Literal (Insert LitBool (Insert TypeBool (Insert Variable ('Empty)))))))))))

type SimplestMoleculeTypeable =  SimplestMolecule


withTestEnv :: forall g m env a.
    ( HasF TypeBool g 
    , MonadReader env m
    ) =>
    Lens.LensLike' Lens.Identity env (InferScope g (UVarOf m)) -> m a -> m a
withTestEnv l act = local (l %~ testEnv) act 
   where testEnv :: InferScope g (UVarOf m) -> InferScope g (UVarOf m)
         testEnv e = e { _varSchemes = ScopeTypes boolAlphabet } 
         boolAlphabet :: Map.Map Name (HFlip GTerm (Molecule (VariantF g)) # (UVarOf m)) 
         boolAlphabet = Map.fromList $ (zip (Name <$> ((:"") <$> ['a'..'z']))
                                            (cycle [MkHFlip (GBody (Molecule (toVariantF TypeBool)))]))

         
withCNFTestEnv :: forall g m env a.
    ( HasF TypeLiteral g
    , MonadReader env m
    ) =>
    Lens.LensLike' Lens.Identity env (InferScope g (UVarOf m)) -> m a -> m a
withCNFTestEnv l act = local (l %~ testEnv) act 
   where testEnv :: InferScope g (UVarOf m) -> InferScope g (UVarOf m)
         testEnv e = e { _varSchemes = ScopeTypes boolAlphabet } 
         boolAlphabet :: Map.Map Name (HFlip GTerm (Molecule (VariantF g)) # (UVarOf m)) 
         boolAlphabet = Map.fromList $ (zip (Name <$> ((:"") <$> ['a'..'z']))
                                            (cycle [MkHFlip (GBody (Molecule (toVariantF TypeLiteral)))]))

 

transformToCheckableCNFSimple :: MonadError String m => Pure # (Molecule (VariantF SimplestMolecule))
                                                     -> m (Bool, (Pure # Molecule (VariantF CNFCore)))
transformToCheckableCNFSimple x = transformToCheckableCNF x

 
inferCNF :: Pure # (Molecule (VariantF CNFCore))
       -> Either (TypeError CNFCore # Pure)
                 (Pure # Scheme (Types CNFCore) (TypeOf (Molecule (VariantF CNFCore)))) 
inferCNF x = execPureInfer (withCNFTestEnv id (inferExpr x))  

inferSimple :: Pure # (Molecule (VariantF SimplestMoleculeTypeable))
       -> Either (TypeError SimplestMoleculeTypeable # Pure)
                 (Pure # Scheme (Types SimplestMoleculeTypeable) (TypeOf (Molecule (VariantF SimplestMoleculeTypeable)))) 
inferSimple x = execPureInfer (withTestEnv id (inferExpr x)) 

parseSomeMol :: Text -> Either (ParseErrorBundle Text Void) (Pure # (Molecule (VariantF SimpleMoleculeP))) 
parseSomeMol = runParser (parser LeftRecursive) "" 


genTest :: IO (Pure # (Molecule (VariantF SimpleMoleculeGen)))
genTest = do
   gend <- genTimeLimited gen 10
   if length (Pretty.render (pPrint gend)) < 20 || length (Pretty.render (pPrint gend)) > 40
      then genTest
      else return gend

main :: IO ()
main = do
    testAbsorption
    putStrLn ">>> Random CNF reduce and solve"
    void $ sequence $ replicate 10 $ do
        putStrLn "random generating"
        gend <- genTest     
        print $ pPrint gend
        putStrLn "parsing"
        hFlush stdout

        case parseSomeMol $ pack $ Pretty.render $ pPrint gend of
             Left err -> error $ show err 
             Right q -> do
                let (ch2, p10 :: Pure # Molecule (VariantF SimplestMolecule)) = exampleTelescope q 
                putStrLn $ "exampleTelescope " ++ show ch2
                print $ pPrint p10
                hFlush stdout


                let p11 :: Pure # Molecule (VariantF SimplestMoleculeTypeable) =
                         dilute (Proxy @Type) $ dilute (Proxy @TypeBool) p10

                case inferSimple p11 of

                    Left typerr -> print $ "inference failed: " ++ (Pretty.render (pPrint typerr))
                    Right inferred -> print $ "inference success: " ++ (Pretty.render (pPrint inferred))


                hFlush stdout

            
                case transformToCheckableCNFSimple p10 of
                    Left typerr -> putStrLn $ "CNF transform failed: " ++ (Pretty.render (pPrint typerr))
                    Right (_, transformed ) -> do
                        putStrLn $ "CNF transform success: " ++ (Pretty.render (pPrint transformed))
                        case inferCNF transformed of
                            Left typerr -> print $ "inference failed: " ++ (Pretty.render (pPrint typerr))
                            Right inferred -> do
                                print $ "inference success: "  ++ (Pretty.render (pPrint inferred))
                                let dil :: (Pure # Molecule (VariantF (Insert FlatConjunction (Insert FlatDisjunction CNFCore)))) = dilute (Proxy @FlatConjunction) $ dilute (Proxy @FlatDisjunction) transformed 
                                case flattenCNF dil of  
                                    Left err -> print $ "couldn't flatten CNF: " ++ err 
                                    Right (_, flatted ) -> 
                                        case extractFlatCNF flatted of
                                            Left fa -> print $ "flat CNF extraction failed: " ++ fa 
                                            Right c -> 
                                               case solveFlatConjunction c of
                                                   Nothing -> putStrLn "no solutions"
                                                   Just sol -> print sol
                                   

                putStrLn ""
                hFlush stdout


