{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
module Atoms.Elements.FOL.Not where
import Atoms.Elements.FOL.TypeBool
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

data Not h = Not h 
  deriving (Eq, Ord, Show, Generic, Foldable, Traversable)

instance Functor Not where
   fmap f (Not n) = Not (f n) 

instance Gen1 IO Not where
  liftGen _ = Not <$> gen 

instance Pretty1 Not where
    liftPrintPrec prec lPrec lvl p (Not a) =
       Pretty.text "!" <> (prec lvl p a)


instance (Ord e) => ASumPrecLR Discriminator (ParsecT e Text m) Not where
    liftASumPrecLR _ p =
      ( 420 
      , try $ do
        _ <- symbol "!" 
        r <- p LeftRecursive
--        r <- (try (p NotLeftRecursive)) <|> p LeftRecursive

        pure $ Not r
      )

instance ( HasF Not g
         , HasF TypeBool g
         , ForAllIn Functor g
         ) => Infer1 m (Molecule (VariantF g)) Not where
    liftInferBody (Not a) = do
       InferredChild aI aT <- inferChild a
       expected <- MkANode <$> newTerm (Molecule (toVariantF TypeBool))
       ((Molecule (toVariantF (Not aI)), ) . MkANode) <$> unify (aT ^. _ANode) (expected ^. _ANode)

instance HasTypeConstraints1 g Not where 
   verifyConstraints1 _ _ = Nothing

instance ZipMatchable1 g Not where
   zipJoin1 (Not l) (Not r) = Just (Not (l :*: r))

-- | injection
iNot :: (HasF Not f, ForAllIn Functor f)
     => Pure # Molecule (VariantF f)
     -> Pure # Molecule (VariantF f)
iNot = Pure . Molecule . toVariantF . Not 


