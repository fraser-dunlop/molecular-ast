{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Atoms.Molecule.Gen where
import Atoms.Molecule.AST
import Control.Concurrent (threadDelay)
import Control.Concurrent.Async (race, AsyncCancelled)
import Control.Exception (catch)
import Data.Random.RVar (RVar, runRVar)
import Data.Random.Source.DevRandom (DevRandom(..))
import Hyper
import Type.Set.Variant
import Type.Set.VariantF
import qualified Data.Random.Extras as RX

-- If all Atoms in the Molecule implement (Gen1 IO) then the Molecule is an instance of (Gen IO)
-- which randomly selects from the Atom generators recursively to generate a Molecule.

instance ( Gen1 IO (VariantF g)
         , ForAllIn Functor g
         ) => Gen IO (Molecule (VariantF g) # Pure) where
    gen = Molecule <$> liftGen (\xs -> runRVar (RX.choice xs) DevURandom) 

instance ( Gen1 IO (VariantF g)
         , ForAllIn Functor g
         ) => Gen IO (Pure # Molecule (VariantF g)) where
    gen = Pure <$> gen


-- | Given a time limit in milliseconds repeatedly try and find an (IO a) that computes in less than
-- that limit. This is useful for random AST generation since the computations can easily explode.
genTimeLimited :: IO a -> Int -> IO a
genTimeLimited g i = do
    res <- race (catch (threadDelay i >> return Nothing) handler) (catch (Just <$> g) handler)
    case res of       
       Right (Just r) -> return r
       _ -> genTimeLimited g i
   where
     handler :: AsyncCancelled -> IO (Maybe a)
     handler _= return Nothing 
