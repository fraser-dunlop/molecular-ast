{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Chemistry.Extractions.CNF.Flattened where
import Atoms.Elements.CNF.Flattened
import Atoms.Molecule.AST
import Data.Type.Equality
import Hyper
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF
import Control.Monad.ST.Trans
import Control.Monad.Except


-- This throws an exception when we reach the node to be extracted 
-- in general it would be more sensible to do this in the State monad
class ( HasF FlatConjunction f
      , ForAllIn Functor f
      , ForAllIn Foldable f
      , ForAllIn Traversable f
      , Follow (Locate FlatConjunction f) f ~ FlatConjunction
      , FromSides (Locate FlatConjunction f)
      , MonadError (FlatConjunction ()) m
      ) => ExtractFlatCNF1 m f where
    extractFlatCNF1 :: STRef s Bool
                    -> VariantF f (Pure # Molecule (VariantF f))
                    -> STT s m (Pure # Molecule (VariantF f))

instance ( HasF FlatConjunction f
         , ForAllIn Functor f
         , ForAllIn Foldable f
         , ForAllIn Traversable f
         , Follow (Locate FlatConjunction f) f ~ FlatConjunction
         , FromSides (Locate FlatConjunction f)
         , MonadError (FlatConjunction ()) m 
         ) => ExtractFlatCNF1 m f where
    extractFlatCNF1 changed (VariantF (tag :: SSide ss) res) = 
        case testEquality tag (fromSides @(Locate FlatConjunction f)) of
            Just Refl -> throwError $ (\_ -> ()) <$> res
            Nothing -> pureVNode $ VariantF tag res 


-- This transforms the exception since the exception is expected
-- if there is no exception that becomes the exception
class ( HasF FlatConjunction f
      , ForAllIn Functor f
      , ForAllIn Foldable f
      , ForAllIn Traversable f
      , Follow (Locate FlatConjunction f) f ~ FlatConjunction
      , FromSides (Locate FlatConjunction f)
      , MonadError String m
      ) => ExtractFlatCNF m f where
    extractFlatCNF :: Pure # Molecule (VariantF f)
                -> m (FlatConjunction ())


instance ( HasF FlatConjunction f
         , ForAllIn Functor f
         , ForAllIn Foldable f
         , ForAllIn Traversable f
         , Follow (Locate FlatConjunction f) f ~ FlatConjunction
         , FromSides (Locate FlatConjunction f)
         , MonadError String m
         ) => ExtractFlatCNF m f where
    extractFlatCNF molecule = do
        let e = runExcept $ catchError (runSTT $ do
                               changed <- newSTRef False
                               _ <- foldMoleculeM (extractFlatCNF1 changed) molecule
                               pure Nothing) (pure . Just)
        case e of 
           Left _ -> throwError "extractFlatCNF: the impossible happened! Are you okay?" 
           Right Nothing -> throwError "extractFlatCNF: FlatConjunction Atom not found"
           Right (Just f) -> pure f
