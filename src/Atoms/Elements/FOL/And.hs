{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
module Atoms.Elements.FOL.And where
import Atoms.Elements.FOL.TypeBool
import Atoms.Molecule.AST
import Atoms.Molecule.HasTypeConstraints
import Atoms.Molecule.Infer1
import Atoms.Molecule.ScopeTypes
import Atoms.Molecule.Parser
import Atoms.Molecule.Pretty
import Atoms.Molecule.ZipMatchable
import Control.Lens.Operators
import Control.Lens.Prism
import Data.Text (Text, pack)
import Data.Type.Equality
import qualified Data.Random.Extras as RX
import Data.Random.RVar (RVar, runRVar)
import Data.Random.Source.DevRandom (DevRandom(..))
import GHC.Generics
import Hyper
import Hyper.Class.ZipMatch
import Hyper.Infer
import Hyper.Unify
import Hyper.Unify.New
import qualified Text.Megaparsec.Char.Lexer as L
import qualified Text.PrettyPrint as Pretty
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF


data And h = And h h  
  deriving (Eq, Ord, Show, Generic, Foldable, Traversable)

instance Functor And where
   fmap f (And l r) = And (f l) (f r) 

instance Gen1 IO And where
  liftGen _ = And <$> gen <*> gen

instance Pretty1 And where
    liftPrintPrec prec lPrec lvl p (And a b) =
       ((prec lvl p a) <+> Pretty.text "/\\" <+> (prec lvl p b)) & Pretty.parens 



instance (Ord e) => ASumPrecLR Discriminator (ParsecT e Text m) And where
    liftASumPrecLR NotLeftRecursive _ = ( minBound, empty )
    liftASumPrecLR LeftRecursive p =
      ( 420 
      , try $ do
        l <- p NotLeftRecursive
        _ <- symbol "/\\" 
        r <- (try (p NotLeftRecursive)) <|> p LeftRecursive
        pure $ And l r
      )

instance ( HasF And g
         , HasF TypeBool g
         , ForAllIn Functor g
         ) => Infer1 m (Molecule (VariantF g)) And where
    liftInferBody (And a b) = do
       InferredChild aI aT <- inferChild a
       InferredChild bI bT <- inferChild b
       expected <- MkANode <$> newTerm (Molecule (toVariantF TypeBool))
       unify (aT ^. _ANode) (expected ^. _ANode)
       ((Molecule (toVariantF (And aI bI)), ) . MkANode) <$> unify (aT ^. _ANode) (bT ^. _ANode)

instance HasTypeConstraints1 g And where 
   verifyConstraints1 _ _ = Nothing

instance ZipMatchable1 g And where
   zipJoin1 (And l0 r0) (And l1 r1) = Just (And (l0 :*: l1) (r0 :*: r1)) 

-- | injection
iAnd :: (HasF And f, ForAllIn Functor f)
     => Pure # Molecule (VariantF f)
     -> Pure # Molecule (VariantF f)
     -> Pure # Molecule (VariantF f)
iAnd l r = Pure $ Molecule $ toVariantF (And l r)


