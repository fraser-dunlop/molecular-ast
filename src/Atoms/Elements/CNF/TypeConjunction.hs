{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
module Atoms.Elements.CNF.TypeConjunction where
import Atoms.Elements.Generic.Type
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

data TypeConjunction h = TypeConjunction
  deriving (Eq, Ord, Show, Generic, Foldable, Traversable)


instance Functor TypeConjunction where
   fmap f TypeConjunction = TypeConjunction

instance Gen1 IO TypeConjunction where
  liftGen _ = pure TypeConjunction 

instance Pretty1 TypeConjunction where
    liftPrintPrec _ _ _ _ TypeConjunction = Pretty.text "TypeConjunction"

instance (Ord e) => ASumPrecLR Discriminator (ParsecT e Text m) TypeConjunction where
    liftASumPrecLR _ p = ( minBound, empty )
--      ( -188
--      , try $ do
--          _ <- symbol "TypeConjunction"
--          pure TypeConjunction
--      )

instance ( HasF Type g
         , HasF TypeConjunction g
         , ForAllIn Functor g
         ) => Infer1 m (Molecule (VariantF g)) TypeConjunction where
    liftInferBody TypeConjunction = do
       newTerm (Molecule (toVariantF (Type 0))) <&> (Molecule (toVariantF TypeConjunction), ) . MkANode 


instance HasTypeConstraints1 g TypeConjunction where 
   verifyConstraints1 _ _ = Nothing

instance ZipMatchable1 g TypeConjunction where
   zipJoin1 _ _ = Just TypeConjunction 


