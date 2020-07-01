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


-- | When writing a left recursive parser fragment
--         - match the Discriminator and parse empty on NotLeftRecursive
--         - match the LeftRecursive Discriminator and
--           - parse the left recursive branch by passing NotLeftRecursive to the sub-parser
--           - parse other recursive branches by try NotLeftRecursive <|> LeftRecursive
--   When writing a non left recursive parser fragment
--         - ignore the Discriminator pass LeftRecursive to sub-parsers
data Discriminator = LeftRecursive | NotLeftRecursive


-- | Things that can be parsed
class Parser m a where
    parser :: Discriminator -> m a

-- When all the components of a VariantF are ASumPrecLR then each can instance
-- be looked up (using type level shenanigans) and tried in parallel
-- since (VariantF g) is an instance of ASumPrecLR when all f's in g are instances of ASumPrecLR.

-- Molecule with Pure nest type can be parsed with this neat mutually recursive pair of instances
-- so long as (VariantF g) has a Asum1 instance.
instance ( Ord e
         , ASumPrecLR Discriminator (ParsecT e Text m) (VariantF g)
         , ForAllIn Functor g)
         => Parser (ParsecT e Text m) (Molecule (VariantF g) # Pure) where
    parser d = Molecule <$> snd (liftASumPrecLR d parser)
    -- ^. TODO can column and line numbers be embedded in Molecule so they can be used in 
    -- providing informative type errors

-- Pure with Molecule nest type can be parsed with this neat mutually recursive pair of instances
-- so long as (VariantF g) has a ASumPrecLR instance.
instance ( Ord e
         , ASumPrecLR Discriminator (ParsecT e Text m) (VariantF g)
         , ForAllIn Functor g)
         => Parser (ParsecT e Text m) (Pure # Molecule (VariantF g)) where


    parser d = Pure <$> parser d 


