{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
module Atoms.Elements.Variable where
import Atoms.Elements.Name
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
import Hyper.Type.AST.Var
import qualified Text.PrettyPrint as Pretty
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF

data Variable h = Variable String 
   deriving stock Show
   deriving (Eq, Ord, Generic, Generic1, Foldable, Traversable) 

instance Functor Variable where
   fmap f (Variable i) = Variable i 

qVarPrism :: forall g .
             ( ForAllIn Functor g
             , HasF Variable g
             , Follow (Locate Variable g) g ~ Variable
             , FromSides (Locate Variable g)
             ) => forall f . Prism' ((Molecule (VariantF g)) f) Name 
qVarPrism = prism (\(Name i) -> Molecule $ toVariantF $ Variable i) 
                  (\(Molecule (VariantF ss res)) -> 
                      case testEquality ss (fromSides @(Locate Variable g)) of
                         Just Refl ->
                             case res of
                                 Variable i -> Right $ Name i
                         Nothing -> Left $ Molecule $ VariantF ss res 
                  )

instance Gen1 IO Variable where
  liftGen _ = do
     Variable <$> runRVar ((RX.choice (((:"") <$> ['a'..'z'])))) DevURandom

instance Pretty1 Variable where
    liftPrintPrec _ _ _ _ (Variable i) = Pretty.text i 

instance (Ord e) => ASumPrecLR Discriminator (ParsecT e Text m) Variable where
    liftASumPrecLR _ p =
      ( 0
      , try $ do
          Variable <$> lexeme ((:) <$> letterChar <*> many alphaNumChar <?> "Variable")
      )

instance ( HasF Variable g
         , ForAllIn Functor g
         , HasScope m (ScopeTypes g) 
         , VarType Name (Molecule (VariantF g))
         , TypeOf (Molecule (VariantF g)) ~ (Molecule (VariantF g))
         ) => Infer1 m (Molecule (VariantF g)) Variable where
    liftInferBody (Variable v) = do
       getScope >>= varType (Proxy @(Molecule (VariantF g))) (Name v) <&> MkANode <&> (Molecule (toVariantF (Variable v)), )       


instance HasTypeConstraints1 g Variable where
    verifyConstraints1 _ (Variable v) = Variable v & Just

instance ZipMatchable1 g Variable where
   zipJoin1 (Variable l) (Variable r) = if l == r then Just (Variable l) else Nothing 

iVariable :: (ForAllIn Functor f, HasF Variable f) => String -> Pure # Molecule (VariantF f)
iVariable = Pure . Molecule . toVariantF . Variable 
