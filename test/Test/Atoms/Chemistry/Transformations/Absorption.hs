{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fplugin=Type.Compare.Plugin -fconstraint-solver-iterations=1000 -freduction-depth=10000 #-}
module Test.Atoms.Chemistry.Transformations.Absorption
  ( testAbsorption
  ) where
import Atoms.Chemistry.Cascades.PropCalc.Absorption
import Atoms.Chemistry.Reductions.RemoveParens
import Atoms.Elements.Generic.Parens
import Atoms.Elements.Generic.Type
import Atoms.Elements.Generic.Variable
import Atoms.Elements.PropCalc.And
import Atoms.Elements.PropCalc.Not
import Atoms.Elements.PropCalc.Or
import Atoms.Elements.PropCalc.TypeBool
import Atoms.Molecule.AST
import Atoms.Molecule.Parser
import Atoms.Molecule.Pretty
import Data.Text (Text, pack, unpack)
import Data.Void
import Hyper
import Hyper.Type.Pure()
import Text.Megaparsec()
import qualified Text.PrettyPrint as Pretty
import Type.Set
import Type.Set.VariantF

tests :: [(Text, Text)]
tests = [("p /\\ (p \\/ q)", "p")
        ,("p /\\ (q \\/ p)", "p")
        ,("p /\\ (p \\/ !!q)", "p")  
        ,("p /\\ ((!!q) \\/ p)", "p")  --TODO Parser fix. Note that without the parens aroung !!q this parses as !!(q \/ p)

        ,("(p \\/ q) /\\ p)", "p")
        ,("(q \\/ p) /\\ p)", "p")
        ,("(p \\/ !!q) /\\ p)", "p")
        ,("((!!q) \\/ p) /\\ p)", "p")
        ,("(!p) /\\ ((!p) \\/ q)", "!p")
        ,("(!p) /\\ (q \\/ (!p))", "!p")
        ,("((!p) \\/ q) /\\ !p)", "!p")
        ,("(q \\/ !p) /\\ !p)", "!p")
        ,("(Type \\/ !p) /\\ !p)", "!p")

        ]

testAbsorption :: IO ()
testAbsorption = do
   putStrLn ">>> Testing Absorption" 
   results <- sequence (absorptionTest <$> tests)
   let numtests = length results 
   let passes = length (filter id results)
   putStrLn $ unpack ("    " <> pack (show passes) <> "/" <> pack (show numtests) <> " passed.")

absorptionTest :: (Text, Text) -> IO Bool
absorptionTest (input, expected) = do
   case parseAbsorbable input of
      Left err -> do
         print err 
         return False
      Right ast -> do
         let (_,ast_without_parens :: (Pure # Molecule (VariantF Absorbable))) = removeParens ast
         let (_,res) = absorptionFixed ast_without_parens
         let output = pack (Pretty.render (pPrint res))
         if output == expected 
           then return True 
           else do
             putStrLn $ unpack $ "   Failure!\n"
                              <> "      input:    " <> input <> "\n"
                              <> "      expected: " <> expected  <> "\n"
                              <> "      observed: " <> output <> "\n"
             return False

type Absorbable = (Insert And
                  (Insert Not
                  (Insert Or
                  (Insert Variable
                  (Insert Type
                  (Insert TypeBool 'Empty))))))

parseAbsorbable :: Text -> Either (ParseErrorBundle Text Void) (Pure # (Molecule (VariantF (Insert Parens Absorbable))))
parseAbsorbable = runParser (parser LeftRecursive) ""


