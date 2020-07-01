{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
module Atoms.Elements.CNF.TypeLiteral where
import Atoms.Elements.Type
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
import Hyper.Unify.New
import qualified Text.Megaparsec.Char.Lexer as L
import qualified Text.PrettyPrint as Pretty
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF

data TypeLiteral h = TypeLiteral
  deriving (Eq, Ord, Show, Generic, Foldable, Traversable)


instance Functor TypeLiteral where
   fmap f TypeLiteral = TypeLiteral

instance Gen1 IO TypeLiteral where
  liftGen _ = pure TypeLiteral 

instance Pretty1 TypeLiteral where
    liftPrintPrec _ _ _ _ TypeLiteral = Pretty.text "TypeLiteral"

instance (Ord e) => ASumPrecLR Discriminator (ParsecT e Text m) TypeLiteral where
    liftASumPrecLR _ p = ( minBound, empty )
--      ( -188
--      , try $ do
--          _ <- symbol "TypeLiteral"
--          pure TypeLiteral
--      )

instance ( HasF Type g
         , HasF TypeLiteral g
         , ForAllIn Functor g
         ) => Infer1 m (Molecule (VariantF g)) TypeLiteral where
    liftInferBody TypeLiteral = do
       newTerm (Molecule (toVariantF (Type 0))) <&> (Molecule (toVariantF TypeLiteral), ) . MkANode 


instance HasTypeConstraints1 g TypeLiteral where 
   verifyConstraints1 _ _ = Nothing

instance ZipMatchable1 g TypeLiteral where
   zipJoin1 _ _ = Just TypeLiteral 


