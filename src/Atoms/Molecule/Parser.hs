{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Molecule.Parser (
    module Atoms.Molecule.Parser
  , module Text.Megaparsec
  , module Text.Megaparsec.Char
  ) where
import Atoms.Molecule.AST
import Data.Text (Text)
import Hyper
import Text.Megaparsec
import Text.Megaparsec.Char 
import qualified Text.Megaparsec.Char.Lexer as L 
import Type.Set.Variant
import Type.Set.VariantF

-- | This module makes some bold parsing decisions in constructing a generic parser for Molecules
--  like allowing comments, consuming white-space, and allowing any term in the language to be in
--  parens (you lisp?)
--  This is likely to be revised to become more generic in the future.
--
--  Also thinking about whether ASumPrec1 is powerful enough. Do we need be context aware? 

sc :: (Ord e) => ParsecT e Text m () 
sc = L.space
  space1
  (L.skipLineComment "//")
  (L.skipBlockComment "/*" "*/")

lexeme :: (Ord e) => ParsecT e Text m a -> ParsecT e Text m a
lexeme = L.lexeme sc

symbol :: (Ord e) => Text -> ParsecT e Text m Text 
symbol = L.symbol sc

parens :: (Ord e) => ParsecT e Text m a -> ParsecT e Text m a
parens = between (symbol "(") (symbol ")")

maybeInParens :: (Ord e) => ParsecT e Text m a -> ParsecT e Text m a
maybeInParens p = try (parens p) <|> p


data Discriminator = LeftRecursive | NotLeftRecursive


-- | Things that can be parsed
class Parser m a where
    parser :: Discriminator -> m a

-- When all the components of a VariantF are ASum1 then each can instance
-- be looked up (using type level shenanigans) and tried in parallel
-- since (VariantF g) is an instance of ASum1 when all f's in g are instances of ASum1.

-- Molecule with Pure nest type can be parsed with this neat mutually recursive pair of instances
-- so long as (VariantF g) has a Asum1 instance.
instance ( Ord e
         , ASumPrecLR Discriminator (ParsecT e Text m) (VariantF g)
         , ForAllIn Functor g)
         => Parser (ParsecT e Text m) (Molecule (VariantF g) # Pure) where
    parser d = Molecule <$> snd (liftASumPrecLR d parser)

-- Pure with Molecule nest type can be parsed with this neat mutually recursive pair of instances
-- so long as (VariantF g) has a ASum1 instance.
instance ( Ord e
         , ASumPrecLR Discriminator (ParsecT e Text m) (VariantF g)
         , ForAllIn Functor g)
         => Parser (ParsecT e Text m) (Pure # Molecule (VariantF g)) where
    parser d = Pure <$> parser d


