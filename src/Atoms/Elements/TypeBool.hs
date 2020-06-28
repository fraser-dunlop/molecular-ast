{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
module Atoms.Elements.TypeBool where
import Atoms.Elements.Type
import Atoms.Molecule.AST
import Atoms.Molecule.Infer1
import Atoms.Molecule.ScopeTypes
import Atoms.Molecule.Parser
import Atoms.Molecule.Pretty
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

data TypeBool h = TypeBool
  deriving (Eq, Ord, Show, Generic)


instance Functor TypeBool where
   fmap f TypeBool = TypeBool

instance Gen1 IO TypeBool where
  liftGen _ = pure TypeBool 

instance Pretty1 TypeBool where
    liftPrintPrec _ _ _ _ TypeBool = Pretty.text "TypeBool"

instance (Ord e) => ASumPrecLR Discriminator (ParsecT e Text m) TypeBool where
    liftASumPrecLR _ p =
      ( 188
      , try $ do
          _ <- symbol "TypeBool"
          pure TypeBool
      )

instance ( HasF Type g
         , HasF TypeBool g
         , ForAllIn Functor g
         ) => Infer1 m (Molecule (VariantF g)) TypeBool where
    liftInferBody TypeBool = do
       newTerm (Molecule (toVariantF (Type 0))) <&> (Molecule (toVariantF TypeBool), ) . MkANode 

