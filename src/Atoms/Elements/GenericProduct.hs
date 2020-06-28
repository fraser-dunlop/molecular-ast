{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
module Atoms.Elements.GenericProduct where
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

-- Like GHC.Generics.:*:

data GenericProduct h = GenericProduct h h 
  deriving (Eq, Ord, Show, Generic)


instance Functor GenericProduct where
   fmap f (GenericProduct l r) = GenericProduct (f l) (f r) 

instance Gen1 IO GenericProduct where
  liftGen _ = GenericProduct <$> gen <*> gen 

instance Pretty1 GenericProduct where
    liftPrintPrec prec _ lvl p (GenericProduct l r) =
        Pretty.text "GenericProduct" Pretty.<+> prec lvl p l Pretty.<+> prec lvl p r 

instance (Ord e) => ASumPrec1 (ParsecT e Text m) GenericProduct where
    liftASumPrec p =
      ( 42
      , do
          _ <- symbol "GenericProduct"
          GenericProduct <$> p <*> p
      )

instance ( HasF GenericProduct g
         , ForAllIn Functor g
         ) => Infer1 m (Molecule (VariantF g)) GenericProduct where
    liftInferBody (GenericProduct l r) = undefined -- should be GenericProduct (TypeOf l) (TypeOf r) I think 


instance ZipMatchable1 g GenericProduct where
   zipJoin1 (GenericProduct ll lr) (GenericProduct rl rr) = Just (GenericProduct (ll :*: rl) (lr :*: rr)) 
