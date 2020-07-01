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
--import           FOL 

import qualified Text.PrettyPrint as Pretty

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

import Atoms.Chemistry.Cascades.DeMorgan

import Atoms.Chemistry.Reductions.RemoveParens

import Atoms.Chemistry.Reductions.EliminateImplies
import Atoms.Chemistry.Reductions.EliminateIfAndOnlyIf
import Atoms.Chemistry.Transformations.DeMorgan
import Atoms.Chemistry.Transformations.DoubleNegation
import Atoms.Chemistry.Telescopes.Example
import Atoms.Chemistry.Dilution
import Atoms.Chemistry.Concentration


import Atoms.Elements.CNF.TypeDisjunction
import Atoms.Elements.CNF.TypeConjunction
import Atoms.Elements.CNF.TypeLiteral
import Atoms.Elements.CNF.Literal
import Atoms.Elements.CNF.Disjunction
import Atoms.Elements.CNF.Conjunction
import Atoms.Chemistry.Reductions.CNF.Literals
import Atoms.Chemistry.Telescopes.CNF.Checkable


import Data.Proxy()

import Hyper.Unify.New()
import Hyper.Unify.Generalize()

import qualified Data.Map as Map()

import Text.Megaparsec()
import Data.Void
import Data.Text (Text, pack)


type SimpleMoleculeP = (Insert Parens SimpleMolecule)


type SimpleMoleculeGen = (Insert Implies 
                         (Insert IfAndOnlyIf
                         (Insert Variable 
                         (Insert Not
                         (Insert Or 
                         (Insert And 'Empty))))))


type SimpleMolecule = (Insert Implies SimplerMolecule)

type SimplerMolecule = (Insert IfAndOnlyIf SimplestMolecule) 


type SimplestMolecule = (Insert Variable 
                        (Insert Not
                        (Insert Or 
                        (Insert And (CNFCore)))))




type CNFCore = (Insert TypeLiteral    --including these causes a memory explosion on compilation!!! what!?
               (Insert TypeDisjunction
               (Insert TypeConjunction
               (Insert Conjunction 
               (Insert Disjunction
               (Insert Literal ('Empty)))))))

type SimplestMoleculeTypeable =  (Insert Type 
                                 (Insert TypeBool SimplestMolecule))


withTestEnv :: forall g m env a.
    ( HasF TypeBool g
    , ForAllIn Functor g
    , UnifyGen m (Molecule (VariantF g)), MonadReader env m
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
    , ForAllIn Functor g
    , UnifyGen m (Molecule (VariantF g)), MonadReader env m
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

  

inferSimple :: Pure # (Molecule (VariantF SimplestMoleculeTypeable))
       -> Either (TypeError SimplestMoleculeTypeable # Pure)
                 (Pure # Scheme (Types SimplestMoleculeTypeable) (TypeOf (Molecule (VariantF SimplestMoleculeTypeable)))) 
inferSimple x = execPureInfer (withTestEnv id (inferExpr x)) 

parseSomeMol :: Text -> Either (ParseErrorBundle Text Void) ((Molecule (VariantF SimpleMoleculeP)) # Pure) 
parseSomeMol = runParser (parser LeftRecursive) "" 


genTest :: IO (Pure # (Molecule (VariantF SimpleMoleculeGen)))
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

--                putStrLn "doubleNegation"
--                let p4 = foldMolecule doubleNegation p3 
--                print $ pPrint p4
--
--                putStrLn "deMorganNegationOfConjunctionFixed"
--                let p5 = deMorganNegationOfConjunctionFixed p4 
--                print $ fst p5
--                print $ pPrint $ snd p5
--                putStrLn "deMorganNegationOfDisjunctionFixed"
--                let p6 = deMorganNegationOfDisjunctionFixed $ snd p5
--                print $ fst p6
--                print $ pPrint $ snd p6

--                putStrLn "doubleNegation"
--                let p7 = foldMolecule doubleNegation $ snd p6 
--                print $ pPrint p7

                let (ch, p8 :: Pure # Molecule (VariantF SimplerMolecule)) = reduction (Pure q) 
                putStrLn $ "reduction " ++ show ch
                print $ pPrint p8


                let (ch1, p9 :: Pure # Molecule (VariantF SimplestMolecule)) = eliminateIfAndOnlyIf p8 
                putStrLn $ "exampleIfAndOnlyIf " ++ show ch1
                print $ pPrint p9


                let (ch2, p10 :: Pure # Molecule (VariantF SimplestMolecule)) = exampleTelescope (Pure q) 
                putStrLn $ "exampleTelescope " ++ show ch2
                print $ pPrint p10


                let p11 :: Pure # Molecule (VariantF SimplestMoleculeTypeable) =
                         dilute (Proxy @Type) $ dilute (Proxy @TypeBool) p10

                case inferSimple p11 of

                    Left typerr -> print $ "inference failed: " ++ (Pretty.render (pPrint typerr))
                    Right inferred -> print $ "inference success: " ++ (Pretty.render (pPrint inferred))


            
                case transformToCheckableCNFSimple p9 of
                    Left typerr -> print $ "CNF inference failed: " ++ (Pretty.render (pPrint typerr))
                    Right (_, inferred) -> print $ "CNF inference success: " ++ (Pretty.render (pPrint inferred))

                putStrLn ""


