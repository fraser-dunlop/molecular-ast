{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
module Atoms.Elements.Parens where
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

data Parens h = Parens h 
  deriving (Eq, Ord, Show, Generic, Foldable, Traversable)

instance Functor Parens where
   fmap f (Parens n) = Parens (f n) 

instance Gen1 IO Parens where
  liftGen _ = Parens <$> gen 

instance Pretty1 Parens where
    liftPrintPrec prec lPrec lvl p (Parens a) =
       (prec lvl p a) & Pretty.parens


instance (Ord e) => ASumPrecLR Discriminator (ParsecT e Text m) Parens where
    liftASumPrecLR _ p =
      ( -10000 
      , Parens <$> parens (p LeftRecursive)
      )

instance ( HasF Parens g
         , ForAllIn Functor g
         ) => Infer1 m (Molecule (VariantF g)) Parens where
    liftInferBody (Parens a) = do
       InferredChild aI aT <- inferChild a
       pure (Molecule (toVariantF (Parens aI)), MkANode (aT ^. _ANode ))

instance HasTypeConstraints1 g Parens where 
   verifyConstraints1 _ _ = Nothing

instance ZipMatchable1 g Parens where
   zipJoin1 (Parens l) (Parens r) = Just (Parens (l :*: r))

-- | injection
iParens :: (HasF Parens f, ForAllIn Functor f)
     => Pure # Molecule (VariantF f)
     -> Pure # Molecule (VariantF f)
iParens = Pure . Molecule . toVariantF . Parens 


