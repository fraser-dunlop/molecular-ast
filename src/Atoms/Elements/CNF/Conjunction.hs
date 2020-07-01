{-# LANGUAGE DeriveTraversable    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Elements.CNF.Conjunction where
import Atoms.Elements.CNF.TypeConjunction
import Atoms.Elements.CNF.TypeDisjunction
import Atoms.Elements.CNF.TypeLiteral
import Atoms.Molecule.AST
import Atoms.Molecule.HasTypeConstraints
import Atoms.Molecule.Infer1
import Atoms.Molecule.ScopeTypes
import Atoms.Molecule.TypeError
import Atoms.Molecule.Parser
import Atoms.Molecule.Pretty
import Atoms.Molecule.ZipMatchable
import Control.Lens.Operators
import Control.Lens.Prism
import Control.Monad.Except
import Data.Text (Text, pack)
import Data.Type.Equality
import qualified Data.Random.Extras as RX
import Data.Random.RVar (RVar, runRVar)
import Data.Random.Source.DevRandom (DevRandom(..))
import GHC.Generics
import Hyper
import Hyper.Infer
import Hyper.Unify
import Hyper.Unify.New
import qualified Text.Megaparsec.Char.Lexer as L
import qualified Text.PrettyPrint as Pretty
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF

data Conjunction h = Conjunction h h  
  deriving (Eq, Ord, Show, Generic, Foldable, Traversable)

instance Functor Conjunction where
   fmap f (Conjunction l r) = Conjunction (f l) (f r) 

instance Gen1 IO Conjunction where
  liftGen _ = Conjunction <$> gen <*> gen

instance Pretty1 Conjunction where
    liftPrintPrec prec lPrec lvl p (Conjunction a b) =
       ((prec lvl p a) <+> Pretty.text "\\/" <+> (prec lvl p b)) & Pretty.parens 


instance (Ord e) => ASumPrecLR Discriminator (ParsecT e Text m) Conjunction where
    liftASumPrecLR NotLeftRecursive p = (100, empty)
    liftASumPrecLR LeftRecursive p = ( minBound, empty )
--      ( -499 
--      , try $ do
--        l <- p NotLeftRecursive
--        _ <- symbol "\\/" 
--        r <- p LeftRecursive
--        pure $ Conjunction l r
--      )

instance ( HasF Conjunction g
         , HasF TypeLiteral g
         , HasF TypeConjunction g
         , HasF TypeDisjunction g
         , ForAllIn Functor g
         , MonadError (TypeError g h) m
         ) => Infer1 m (Molecule (VariantF g)) Conjunction where
    liftInferBody (Conjunction a b) = do
       InferredChild aI aT <- inferChild a
       InferredChild bI bT <- inferChild b
       expectedLit <- MkANode <$> newTerm (Molecule (toVariantF TypeLiteral))
       expectedDis <- MkANode <$> newTerm (Molecule (toVariantF TypeDisjunction))
       expectedCon <- MkANode <$> newTerm (Molecule (toVariantF TypeConjunction))
       catchError (unify (aT ^. _ANode) (expectedCon ^. _ANode))
                  (\_ -> catchError (unify (aT ^. _ANode) (expectedDis ^. _ANode))
                                    (\_ -> unify (aT ^. _ANode) (expectedLit ^. _ANode)))
       catchError (unify (bT ^. _ANode) (expectedCon ^. _ANode))
                  (\_ -> catchError (unify (bT ^. _ANode) (expectedDis ^. _ANode))
                                    (\_ -> unify (bT ^. _ANode) (expectedLit ^. _ANode)))
       pure (Molecule (toVariantF (Conjunction aI bI)), MkANode (expectedCon ^. _ANode))

instance HasTypeConstraints1 g Conjunction where 
   verifyConstraints1 _ _ = Nothing

instance ZipMatchable1 g Conjunction where
   zipJoin1 (Conjunction ll rl) (Conjunction lr rr) = Just (Conjunction (ll :*: lr) (rl :*: rr)) 


-- | injection
iConjunction :: (HasF Conjunction f, ForAllIn Functor f)
    => Pure # Molecule (VariantF f)
    -> Pure # Molecule (VariantF f)
    -> Pure # Molecule (VariantF f)
iConjunction l r = Pure $ Molecule $ toVariantF (Conjunction l r)



