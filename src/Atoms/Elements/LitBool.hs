{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
module Atoms.Elements.LitBool where
import Atoms.Elements.TypeBool
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

data LitBool h = LitBool Bool 
  deriving (Eq, Ord, Show, Generic, Generic1)


instance Functor LitBool where
   fmap f (LitBool b) = LitBool b 

instance Gen1 IO LitBool where
  liftGen _ = do
     LitBool <$> runRVar ((RX.choice [True,False])) DevURandom

instance Pretty1 LitBool where
    liftPrintPrec _ _ _ _ (LitBool True) = Pretty.text "True"
    liftPrintPrec _ _ _ _ (LitBool False) = Pretty.text "False"

instance (Ord e) => ASumPrec1 (ParsecT e Text m) LitBool where
    liftASumPrec p =
      ( 42
      , (do
          _ <- symbol "True"
          pure $ LitBool True 
        )
        <|>
        (do
          _ <- symbol "False"
          pure $ LitBool False
        )
      )

instance ( HasF TypeBool g
         , HasF LitBool g
         , ForAllIn Functor g
         ) => Infer1 m (Molecule (VariantF g)) LitBool where
    liftInferBody (LitBool b) = do
       newTerm (Molecule (toVariantF TypeBool)) <&> (Molecule (toVariantF (LitBool b)), ) . MkANode 

