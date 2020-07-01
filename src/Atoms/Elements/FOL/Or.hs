{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
module Atoms.Elements.FOL.Or where
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
import Hyper.Infer
import Hyper.Unify
import Hyper.Unify.New
import qualified Text.Megaparsec.Char.Lexer as L
import qualified Text.PrettyPrint as Pretty
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF

data Or h = Or h h  
  deriving (Eq, Ord, Show, Generic, Foldable, Traversable)

instance Functor Or where
   fmap f (Or l r) = Or (f l) (f r) 

instance Gen1 IO Or where
  liftGen _ = Or <$> gen <*> gen

instance Pretty1 Or where
    liftPrintPrec prec lPrec lvl p (Or a b) =
       ((prec lvl p a) <+> Pretty.text "\\/" <+> (prec lvl p b)) & Pretty.parens 


instance (Ord e) => ASumPrecLR Discriminator (ParsecT e Text m) Or where
    liftASumPrecLR NotLeftRecursive p = ( minBound, empty )
    liftASumPrecLR LeftRecursive p =
      ( (420 :: Int) 
      , try $ do
        l <- p NotLeftRecursive
        _ <- symbol "\\/" 
        r <- (try (p NotLeftRecursive)) <|> p LeftRecursive
        pure $ Or l r
      )

instance ( HasF Or g
         , HasF TypeBool g
         , ForAllIn Functor g
         ) => Infer1 m (Molecule (VariantF g)) Or where
    liftInferBody (Or a b) = do
       InferredChild aI aT <- inferChild a
       InferredChild bI bT <- inferChild b
       expected <- MkANode <$> newTerm (Molecule (toVariantF TypeBool))
       unify (aT ^. _ANode) (expected ^. _ANode)
       ((Molecule (toVariantF (Or aI bI)), ) . MkANode) <$> unify (aT ^. _ANode) (bT ^. _ANode)

instance HasTypeConstraints1 g Or where 
   verifyConstraints1 _ _ = Nothing

instance ZipMatchable1 g Or where
   zipJoin1 (Or ll rl) (Or lr rr) = Just (Or (ll :*: lr) (rl :*: rr)) 


-- | injection
iOr :: (HasF Or f, ForAllIn Functor f)
    => Pure # Molecule (VariantF f)
    -> Pure # Molecule (VariantF f)
    -> Pure # Molecule (VariantF f)
iOr l r = Pure $ Molecule $ toVariantF (Or l r)



