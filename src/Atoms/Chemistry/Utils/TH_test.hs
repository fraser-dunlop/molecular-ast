{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Chemistry.Utils.TH_test where
import Atoms.Chemistry.Utils.TH
import Language.Haskell.TH
import Atoms.Elements.PropCalc.Not
import Atoms.Elements.PropCalc.And
import Atoms.Molecule.AST
import Data.Type.Equality
import Hyper
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF
import Data.STRef
import Control.Monad.ST

import qualified GHC.Base
import qualified Hyper.Type.Pure 
import qualified Atoms.Molecule.AST
import Prelude

[transformation|
--someTransformation changed (Not (Not a)) = do 
--  writeSTRef changed True
--  pure a
--someTransformation changed (Not (And a b)) = b
someTransformation changed (Not a) = a
someTransformation changed a = a

|]
