{-# LANGUAGE DeriveTraversable    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Elements.CNF.Disjunction where
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

data Disjunction h = Disjunction h h  
  deriving (Eq, Ord, Show, Generic, Foldable, Traversable)

instance Functor Disjunction where
   fmap f (Disjunction l r) = Disjunction (f l) (f r) 

instance Gen1 IO Disjunction where
  liftGen _ = Disjunction <$> gen <*> gen

instance Pretty1 Disjunction where
    liftPrintPrec prec lPrec lvl p (Disjunction a b) =
       ((prec lvl p a) <+> Pretty.text "\\/" <+> (prec lvl p b)) & Pretty.parens 


instance (Ord e) => ASumPrecLR Discriminator (ParsecT e Text m) Disjunction where
    liftASumPrecLR NotLeftRecursive p = (100, empty)
    liftASumPrecLR LeftRecursive p =
      ( -419 
      , try $ do
        l <- p NotLeftRecursive
        _ <- symbol "\\/" 
        r <- p LeftRecursive
        pure $ Disjunction l r
      )

instance ( HasF Disjunction g
         , HasF TypeLiteral g
         , HasF TypeDisjunction g
         , ForAllIn Functor g
         , MonadError (TypeError g h) m
         ) => Infer1 m (Molecule (VariantF g)) Disjunction where
    liftInferBody (Disjunction a b) = do
       InferredChild aI aT <- inferChild a
       InferredChild bI bT <- inferChild b
       expectedLit <- MkANode <$> newTerm (Molecule (toVariantF TypeLiteral))
       expectedDis <- MkANode <$> newTerm (Molecule (toVariantF TypeDisjunction))
       catchError (unify (aT ^. _ANode) (expectedDis ^. _ANode))
                  (\_ -> unify (aT ^. _ANode) (expectedLit ^. _ANode))
       catchError (unify (bT ^. _ANode) (expectedDis ^. _ANode))
                  (\_ -> unify (bT ^. _ANode) (expectedLit ^. _ANode))
       pure (Molecule (toVariantF (Disjunction aI bI)), MkANode (expectedDis ^. _ANode))

instance HasTypeConstraints1 g Disjunction where 
   verifyConstraints1 _ _ = Nothing

instance ZipMatchable1 g Disjunction where
   zipJoin1 (Disjunction ll rl) (Disjunction lr rr) = Just (Disjunction (ll :*: lr) (rl :*: rr)) 


-- | injection
iDisjunction :: (HasF Disjunction f, ForAllIn Functor f)
    => Pure # Molecule (VariantF f)
    -> Pure # Molecule (VariantF f)
    -> Pure # Molecule (VariantF f)
iDisjunction l r = Pure $ Molecule $ toVariantF (Disjunction l r)



