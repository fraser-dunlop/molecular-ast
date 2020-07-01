{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
module Atoms.Elements.CNF.TypeDisjunction where
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

data TypeDisjunction h = TypeDisjunction
  deriving (Eq, Ord, Show, Generic, Foldable, Traversable)


instance Functor TypeDisjunction where
   fmap f TypeDisjunction = TypeDisjunction

instance Gen1 IO TypeDisjunction where
  liftGen _ = pure TypeDisjunction 

instance Pretty1 TypeDisjunction where
    liftPrintPrec _ _ _ _ TypeDisjunction = Pretty.text "TypeDisjunction"

instance (Ord e) => ASumPrecLR Discriminator (ParsecT e Text m) TypeDisjunction where
    liftASumPrecLR _ p =
      ( -188
      , try $ do
          _ <- symbol "TypeDisjunction"
          pure TypeDisjunction
      )

instance ( HasF Type g
         , HasF TypeDisjunction g
         , ForAllIn Functor g
         ) => Infer1 m (Molecule (VariantF g)) TypeDisjunction where
    liftInferBody TypeDisjunction = do
       newTerm (Molecule (toVariantF (Type 0))) <&> (Molecule (toVariantF TypeDisjunction), ) . MkANode 


instance HasTypeConstraints1 g TypeDisjunction where 
   verifyConstraints1 _ _ = Nothing

instance ZipMatchable1 g TypeDisjunction where
   zipJoin1 _ _ = Just TypeDisjunction 


