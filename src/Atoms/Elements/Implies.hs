{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
module Atoms.Elements.Implies where
import Atoms.Elements.TypeBool
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

data Implies h = Implies h h  
  deriving (Eq, Ord, Show, Generic)

instance Functor Implies where
   fmap f (Implies l r) = Implies (f l) (f r) 

instance Gen1 IO Implies where
  liftGen _ = Implies <$> gen <*> gen

instance Pretty1 Implies where
    liftPrintPrec prec lPrec lvl p (Implies a b) =
       ((prec lvl p a) <+> Pretty.text "->" <+> (prec lvl p b)) -- & Pretty.parens 



instance (Ord e) => ASumPrecLR Discriminator (ParsecT e Text m) Implies where
    liftASumPrecLR NotLeftRecursive _ = (-100, empty) 
    liftASumPrecLR LeftRecursive p =
      ( 420 
      , try $ do
        l <- p NotLeftRecursive
        _ <- symbol "->" 
        r <- p LeftRecursive
        pure $ Implies l r
      )

instance ( HasF Implies g
         , HasF TypeBool g
         , ForAllIn Functor g
         ) => Infer1 m (Molecule (VariantF g)) Implies where
    liftInferBody (Implies a b) = do
       InferredChild aI aT <- inferChild a
       InferredChild bI bT <- inferChild b
       expected <- MkANode <$> newTerm (Molecule (toVariantF TypeBool))
       unify (aT ^. _ANode) (expected ^. _ANode)
       ((Molecule (toVariantF (Implies aI bI)), ) . MkANode) <$> unify (aT ^. _ANode) (bT ^. _ANode)

instance HasTypeConstraints1 g Implies where 
   verifyConstraints1 _ _ = Nothing

instance ZipMatchable1 g Implies where
   zipJoin1 (Implies ll rl) (Implies lr rr) = Just (Implies (ll :*: lr) (rl :*: rr)) 


-- | injection
iImplies :: (HasF Implies f, ForAllIn Functor f)
     => Pure # Molecule (VariantF f)
     -> Pure # Molecule (VariantF f)
     -> Pure # Molecule (VariantF f)
iImplies l r = Pure $ Molecule $ toVariantF (Implies l r)


