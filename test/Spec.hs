{-# LANGUAGE FlexibleContexts, BlockArguments, OverloadedStrings #-}
{-# OPTIONS_GHC -fplugin=Type.Compare.Plugin -fconstraint-solver-iterations=0 -freduction-depth=0 #-}

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


import Text.Megaparsec
import Data.Void
import Data.Text (Text, pack)


--formula1 :: HPlain FOL
--formula1 =
--    BLamP "x" ("x" `BAndP` (BNotP "x"))
--
--formula2 :: HPlain FOL
--formula2 =
--    BLamP "x" ("x" `BOrP` ("x" `BAndP` (BNotP "x")))
--
--formula3 :: HPlain FOL
--formula3 =
--    BLamP "z" (BLamP "y" (BLamP "x" ("y" `BOrP` ("x" `BAndP` (BNotP "z")))))
--
--
--formula4 :: HPlain FOL
--formula4 =
--    BLamP "z" (BLamP "y" (BLamP "x" ("y" `BOrP` (((BLitP True) `BAndP` "x") `BAndP` (BNotP "z")))))
--
--
--impliesFormula1 :: HPlain FOL
--impliesFormula1 =
--    BLamP "z" (BLamP "y" (BLamP "x" ("y" `BImpliesP` ("x" `BAndP` (BNotP "z")))))
--
--ifAndOnlyIfFormula1 :: HPlain FOL
--ifAndOnlyIfFormula1 =
--    BLamP "z" (BLamP "y" (BLamP "x" ("y" `BIfAndOnlyIfP` ("x" `BAndP` (BNotP "z")))))
--
--
--existsFormula1 :: HPlain FOL
--existsFormula1 = BExistsP "x" "x"
--
--
--existsFormula2 :: HPlain FOL
--existsFormula2 = BLamP "y" (BExistsP "x" ("x" `BOrP` "y"))
--
--
--
--forAllFormula1 :: HPlain FOL
--forAllFormula1 = BLamP "y" (BForAllP "z" (BExistsP "x" ("x" `BOrP` ("y" `BAndP` "z"))))
--
--
--
--
--testFOL :: HPlain FOL -> String -> IO Bool
--testFOL p expect =
--    testCommon expr expect pureRes stRes
--    where
--        expr = p ^. hPlain
--        pureRes = execPureInferB (withEnv id (inferExpr expr))
--        stRes = runST (execSTInferB (withEnv Lens._1 (inferExpr expr)))
--
--inferExpr ::
--    forall m t.
--    ( HasInferredType t
--    , Infer m t
--    , HasScheme Types m (TypeOf t)
--    , RTraversable t
--    , RTraversableInferOf t
--    ) =>
--    Pure # t ->
--    m (Pure # Scheme Types (TypeOf t))
--inferExpr x =
--    do
--        inferRes <- infer (wrap (const (Ann (Const ()))) x)
--        result <-
--            inferRes ^# hAnn . Lens._2 . _InferResult . inferredType (Proxy @t)
--            & generalize
--            >>= saveScheme
--        result <$
--            htraverse_
--            ( Proxy @(Infer m) #*# Proxy @RTraversableInferOf #*#
--                \w (Const () :*: InferResult i) ->
--                withDict (inferContext (Proxy @m) w) $
--                htraverse_ (Proxy @(UnifyGen m) #> void . applyBindings) i
--            ) (_HFlip # inferRes)
--
--vecNominalDecl :: Pure # NominalDecl Typ
--vecNominalDecl =
--    _Pure # NominalDecl
--    { _nParams =
--        Types
--        { _tRow = mempty
--        , _tTyp = mempty & Lens.at "elem" ?~ mempty
--        }
--    , _nScheme =
--        Scheme
--        { _sForAlls = Types mempty mempty
--        , _sTyp =
--            ( REmptyP
--                & RExtendP "x" (TVarP "elem")
--                & RExtendP "y" (TVarP "elem")
--                & TRecP
--            ) ^. hPlain
--        }
--    }
--
--phantomIntNominalDecl :: Pure # NominalDecl Typ
--phantomIntNominalDecl =
--    _Pure # NominalDecl
--    { _nParams =
--        Types
--        { _tRow = mempty
--        , _tTyp = mempty & Lens.at "phantom" ?~ mempty
--        }
--    , _nScheme =
--        Scheme
--        { _sForAlls = Types mempty mempty
--        , _sTyp = _Pure # TInt
--        }
--    }
--
--mutType :: HPlain Typ
--mutType =
--    TNomP "Mut"
--    Types
--    { _tRow = mempty & Lens.at "effects" ?~ (RVar "effects" & Pure) & QVarInstances
--    , _tTyp = mempty & Lens.at "value" ?~ (TVar "value" & Pure) & QVarInstances
--    }
--
---- A nominal type with foralls:
---- "newtype LocalMut a = forall s. Mut s a"
--localMutNominalDecl :: Pure # NominalDecl Typ
--localMutNominalDecl =
--    _Pure # NominalDecl
--    { _nParams =
--        Types
--        { _tRow = mempty
--        , _tTyp = mempty & Lens.at "value" ?~ mempty
--        }
--    , _nScheme =
--        forAll (Lens.Const ()) (Lens.Identity "effects") (\_ _ -> mutType) ^. _Pure
--    }
--
--returnScheme :: Pure # Scheme Types Typ
--returnScheme =
--    forAll (Lens.Identity "value") (Lens.Identity "effects") $
--    \(Lens.Identity val) _ -> TFunP val mutType
--
--withEnv ::
--    ( UnifyGen m Row, MonadReader env m
--    , HasScheme Types m Typ
--    ) =>
--    Lens.LensLike' Lens.Identity env (InferScope (UVarOf m)) -> m a -> m a
--withEnv l act =
--    do
--        vec <- loadNominalDecl vecNominalDecl
--        phantom <- loadNominalDecl phantomIntNominalDecl
--        localMut <- loadNominalDecl localMutNominalDecl
--        let addNoms x =
--                x
--                & Lens.at "Vec" ?~ vec
--                & Lens.at "PhantomInt" ?~ phantom
--                & Lens.at "LocalMut" ?~ localMut
--        ret <- loadScheme returnScheme
--        let addEnv x =
--                x
--                & nominals %~ addNoms
--                & varSchemes . _ScopeTypes . Lens.at "return" ?~ MkHFlip ret
--        local (l %~ addEnv) act
--
--prettyStyle :: Pretty a => a -> String
--prettyStyle = Pretty.renderStyle (Pretty.Style Pretty.OneLineMode 0 0) . pPrint
--
--prettyPrint :: Pretty a => a -> IO ()
--prettyPrint = putStrLn . prettyStyle
--
--testCommon ::
--    (Pretty (lang # Pure), Pretty a, Eq a) =>
--    Pure # lang ->
--    String ->
--    Either (TypeError # Pure) a ->
--    Either (TypeError # Pure) a ->
--    IO Bool
--testCommon expr expect pureRes stRes =
--    do
--        putStrLn ""
--        prettyPrint expr
--        putStrLn "inferred to:"
--        prettyPrint pureRes
--        filter (not . fst) checks <&> snd & sequence_
--        all fst checks & pure
--    where
--        checks =
--            [ (expect == prettyStyle pureRes, putStrLn ("FAIL! Expected:\n" <> expect))
--            , (pureRes == stRes, putStrLn "FAIL! Different result in ST:" *> prettyPrint stRes)
--            ]
--
--forAll ::
--    (Traversable t, Traversable u) =>
--    t Name -> u Name ->
--    (t (HPlain Typ) -> u (HPlain Row) -> HPlain Typ) ->
--    Pure # Scheme Types Typ
--forAll tvs rvs body =
--    _Pure #
--    Scheme (Types (foralls tvs) (foralls rvs))
--    (body (tvs <&> TVarP) (rvs <&> RVarP) ^. hPlain)
--    where
--        foralls ::
--            ( Foldable f
--            , QVar typ ~ Name
--            , Monoid (TypeConstraintsOf typ)
--            ) =>
--            f Name -> QVars # typ
--        foralls xs =
--            xs ^.. Lens.folded <&> (, mempty)
--            & Map.fromList & QVars
--
--

type SimpleMolecule = (Insert Implies
                      (Insert And 
                      (Insert Or
                      (Insert Not
                      (Insert Type 
                      (Insert Variable 
                      (Insert Atoms.Elements.TypeBool.TypeBool ('Empty))))))))

type SimplerMolecule = (Insert And 
                       (Insert Or
                       (Insert Not
                       (Insert Type 
                       (Insert Variable 
                       (Insert Atoms.Elements.TypeBool.TypeBool ('Empty)))))))


parseSomeMol :: Text -> Either (ParseErrorBundle Text Void) ((Molecule (VariantF SimpleMolecule)) # Pure) 
parseSomeMol = runParser (parser LeftRecursive) "" 



testSomeMol :: Either (ParseErrorBundle Text Void) ((Molecule (VariantF SimpleMolecule)) # Pure) 
testSomeMol = runParser (parser LeftRecursive) "" "a -> b \\/ c" 

shouldParseAs :: (Pure # (Molecule (VariantF SimpleMolecule))) 
shouldParseAs = iVariable "a" `iImplies` (iVariable "b" `iOr` iVariable "c") 


--testSimpleMolecule :: Pure # (Molecule (VariantF SimpleMolecule)) 
--                   -> Either (Pure # TypeError SimpleMolecule) (Pure # (Molecule (VariantF SimpleMolecule)))

--testSimpleMolecule expr  = execPureInfer (inferExpr expr)

foldMolecule :: (ForAllIn Functor f) => ((VariantF f) a -> a) -> Pure # (Molecule (VariantF f)) -> a
foldMolecule f (Pure (Molecule t)) = f (fmap (foldMolecule f) t)

-- | is this causing type checking to diverge?
--elimImp :: Pure # (Molecule (VariantF SimpleMolecule)) -> Pure # (Molecule (VariantF SimplerMolecule))
--elimImp = foldMolecule eliminateImples

--elimImpDecidable :: Pure # (Molecule (VariantF SimplerMolecule))
--elimImpDecidable = foldMolecule eliminateImples shouldParseAs

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
                putStrLn ""
--            let Pure el = elimImp (Pure p) 
--            print $ pPrint el 
--            case testSimpleMolecule (Pure p) of
--                Left _ -> print "type error"
--                Right t -> print $ pPrint t 

--main :: IO ()
--main = do
--    print rewriteWorks
--    print rewriteBothWorks
--    print $ pPrint expr1
--    print $ pPrint expr2
--    putStrLn ""
--    print $ pPrint expr4
--    print $ pPrint expr5
--    case testVarf of
--      Left _ -> print "parse failure"
--      Right omg -> do
--         print "parse success"
--         print $ pPrint omg
--    
--    sequence $ replicate 100 (do
--          tt <- genTest
--          print $ pPrint tt
--        )
--    return ()
 
--main :: IO ()
--main =
--    do
--        numFails <-
--            sequenceA tests
--            <&> filter not <&> length
--        putStrLn ""
--        show numFails <> " tests failed out of " <> show (length tests) & putStrLn
--        when (numFails > 0) exitFailure
--    where
--        tests =
--            [ testFOL formula1 "Right (Bool -> Bool)"
--            , testFOL formula2 "Right (Bool -> Bool)"
--            , testFOL formula3 "Right (Bool -> Bool -> Bool -> Bool)"
--            , testFOL formula4 "Right (Bool -> Bool -> Bool -> Bool)"
--            , testFOL impliesFormula1 "Right (Bool -> Bool -> Bool -> Bool)"
--            , testFOL ifAndOnlyIfFormula1 "Right (Bool -> Bool -> Bool -> Bool)"
--            , testFOL existsFormula1 "Right Bool"
--            , testFOL existsFormula2 "Right (Bool -> Bool)"
--            , testFOL forAllFormula1 "Right (Bool -> Bool)"
--
--            ]

