{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
module Atoms.Elements.CNF.TypeLit where
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

data TypeLit h = TypeLit
  deriving (Eq, Ord, Show, Generic, Foldable, Traversable)


instance Functor TypeLit where
   fmap f TypeLit = TypeLit

instance Gen1 IO TypeLit where
  liftGen _ = pure TypeLit 

instance Pretty1 TypeLit where
    liftPrintPrec _ _ _ _ TypeLit = Pretty.text "TypeLit"

instance (Ord e) => ASumPrecLR Discriminator (ParsecT e Text m) TypeLit where
    liftASumPrecLR _ p =
      ( 188
      , try $ do
          _ <- symbol "TypeLit"
          pure TypeLit
      )

instance ( HasF Type g
         , HasF TypeLit g
         , ForAllIn Functor g
         ) => Infer1 m (Molecule (VariantF g)) TypeLit where
    liftInferBody TypeLit = do
       newTerm (Molecule (toVariantF (Type 0))) <&> (Molecule (toVariantF TypeLit), ) . MkANode 


instance HasTypeConstraints1 g TypeLit where 
   verifyConstraints1 _ _ = Nothing

instance ZipMatchable1 g TypeLit where
   zipJoin1 _ _ = Just TypeLit 


