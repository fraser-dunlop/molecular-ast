{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
module Atoms.Elements.Type where
import Atoms.Elements.GenericProduct
import Atoms.Molecule.AST
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

data Type h = Type Int
  deriving (Eq, Ord, Show, Generic)


instance Functor Type where
   fmap f (Type i) = Type i 

instance Gen1 IO Type where
  liftGen _ = do
     Type <$> runRVar ((RX.choice [0..2])) DevURandom

instance Pretty1 Type where
    liftPrintPrec _ _ _ _ (Type 0) = Pretty.text "Type"
    liftPrintPrec _ _ _ _ (Type i) = Pretty.text "Type" <> Pretty.text (show i) 

instance (Ord e) => ASumPrecLR Discriminator (ParsecT e Text m) Type where
    liftASumPrecLR _ p =
      ( 42
      , (try $ do
          _ <- string "Type"
          d <- L.decimal  
          _ <- sc 
          pure $ Type d 
        )
        <|>
        (try $ do
          _ <- symbol "Type"
          pure $ Type 0
        )
      )

instance ( HasF Type g
         , ForAllIn Functor g
         ) => Infer1 m (Molecule (VariantF g)) Type where
    liftInferBody (Type i) = do
       newTerm (Molecule (toVariantF (Type (i + 1)))) <&> (Molecule (toVariantF (Type i)), ) . MkANode 

instance ZipMatchable1 g Type where
   zipJoin1 (Type l) (Type r) = if l == r then Just (Type l) else Nothing

