{-# LANGUAGE DeriveTraversable    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Elements.CNF.Literal where
import Atoms.Elements.CNF.TypeLit
import Atoms.Elements.Name
import Atoms.Molecule.AST
import Atoms.Molecule.Class.VarType
import Atoms.Molecule.HasTypeConstraints
import Atoms.Molecule.Infer1
import Atoms.Molecule.ScopeTypes
import Atoms.Molecule.Parser
import Atoms.Molecule.Pretty
import Atoms.Molecule.ZipMatchable
import Control.Lens.Operators
import Control.Lens.Prism
import Control.Lens.Review
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
import qualified Text.PrettyPrint as Pretty
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF

data Literal h where
   Positive :: Name -> Literal h
   Negative :: Name -> Literal h
   deriving stock Show
   deriving (Eq, Ord, Generic, Generic1, Foldable, Traversable) 

posLit :: Prism' (Literal h) Name
posLit = prism' Positive (\case
                              Positive nm -> Just nm
                              _ -> Nothing)

negLit :: Prism' (Literal h) Name
negLit = prism' Negative (\case
                              Negative nm -> Just nm
                              _ -> Nothing)

-- Gratuitous use of Prisms 
unwrapLit :: Literal h -> (Name, Name -> Literal g)
unwrapLit (Positive l) = (l, (^. re posLit))
unwrapLit (Negative l) = (l, (^. re negLit))


instance Functor Literal where
   fmap f (Positive i) = Positive i 
   fmap f (Negative i) = Negative i

instance Gen1 IO Literal where
  liftGen _ = do
     cons <- runRVar (RX.choice [Positive, Negative]) DevURandom
     cons . Name <$> runRVar ((RX.choice (((:"") <$> ['a'..'z'])))) DevURandom

instance Pretty1 Literal where
    liftPrintPrec _ _ _ _ (Positive (Name i)) = Pretty.text i 
    liftPrintPrec _ _ _ _ (Negative (Name i)) = Pretty.text "!" <> Pretty.text i 


-- | This is a reduction target and not intended to be parsed
instance (Ord e) => ASumPrecLR Discriminator (ParsecT e Text m) Literal where
    liftASumPrecLR _ p =
      ( 0
      , ( try $ do
          _ <- symbol "!"
          Negative . Name <$> lexeme ((:) <$> letterChar <*> many alphaNumChar <?> "Variable")
        )
        <|>
        (
          Positive . Name <$> lexeme ((:) <$> letterChar <*> many alphaNumChar <?> "Variable")
        )
      )

instance ( HasF Literal g
         , HasF TypeLit g
         , ForAllIn Functor g
         , HasScope m (ScopeTypes g) 
         , VarType m Name (Molecule (VariantF g))
         , TypeOf (Molecule (VariantF g)) ~ (Molecule (VariantF g))
         ) => Infer1 m (Molecule (VariantF g)) Literal where
    liftInferBody (Positive v) = do
       expected <- MkANode <$> newTerm (Molecule (toVariantF TypeLit))
       (pI, pT) <- getScope >>= varType (Proxy @(Molecule (VariantF g))) v
                                  <&> MkANode
                                  <&> (Molecule (toVariantF (Positive v)), )       
       ((pI, ) . MkANode) <$> unify (pT ^. _ANode) (expected ^. _ANode)
    liftInferBody (Negative v) = do
       expected <- MkANode <$> newTerm (Molecule (toVariantF TypeLit))
       (pI, pT) <- getScope >>= varType (Proxy @(Molecule (VariantF g))) v
                                  <&> MkANode
                                  <&> (Molecule (toVariantF (Positive v)), )       
       ((pI, ) . MkANode) <$> unify (pT ^. _ANode) (expected ^. _ANode)


instance HasTypeConstraints1 g Literal where
    verifyConstraints1 _ (Positive v) = Positive v & Just
    verifyConstraints1 _ (Negative v) = Negative v & Just



instance ZipMatchable1 g Literal where
   zipJoin1 (Positive l) (Positive r) = if l == r then Just (Positive l) else Nothing 
   zipJoin1 (Negative l) (Negative r) = if l == r then Just (Negative l) else Nothing 


iPosLiteral :: (ForAllIn Functor f, HasF Literal f) => String -> Pure # Molecule (VariantF f)
iPosLiteral = Pure . Molecule . toVariantF . Positive . Name 

iNegLiteral :: (ForAllIn Functor f, HasF Literal f) => String -> Pure # Molecule (VariantF f)
iNegLiteral = Pure . Molecule . toVariantF . Negative . Name

