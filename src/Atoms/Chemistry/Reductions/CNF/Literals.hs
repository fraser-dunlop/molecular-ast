{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Chemistry.Reductions.CNF.Literals where
import Atoms.Elements.CNF.Literal
import Atoms.Elements.Name
import Atoms.Elements.Not
import Atoms.Elements.Variable
import Atoms.Molecule.AST
import Atoms.Molecule.Pretty
import Data.Type.Equality
import Hyper
import qualified Text.PrettyPrint as Pretty
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF
import Control.Monad.ST.Trans
import Control.Monad.Except

class ( HasF Not f
      , HasF Variable f
      , HasF Literal f
      , HasF Literal t
      , ForAllIn Functor f
      , ForAllIn Foldable f
      , ForAllIn Traversable f
      , ForAllIn Functor t
      , ForAllIn Pretty1 t
      , Insert Not t ~ f
      , Follow (Locate Not f) f ~ Not 
      , FromSides (Locate Not f)
      , Follow (Locate Variable f) f ~ Variable 
      , FromSides (Locate Variable f)
      , Follow (Locate Literal f) f ~ Literal 
      , FromSides (Locate Literal f)
      , Follow (Locate Literal t) t ~ Literal 
      , FromSides (Locate Literal t)
      , MonadError String m
      ) => Literals m f t where
    literals1 :: STRef s Bool
                      -> VariantF f (Pure # Molecule (VariantF t))
                      -> STT s m (Pure # Molecule (VariantF t))
    literals :: Pure # Molecule (VariantF f)
                     -> m (Bool, Pure # Molecule (VariantF t))

instance ( HasF Variable f
         , HasF Not f
         , HasF Literal f
         , HasF Literal t
         , ForAllIn Functor f
         , ForAllIn Foldable f
         , ForAllIn Traversable f
         , ForAllIn Functor t
         , ForAllIn Pretty1 t
         , Insert Not t ~ f
         , Follow (Locate Not f) f ~ Not 
         , FromSides (Locate Not f)
         , Follow (Locate Variable f) f ~ Variable 
         , FromSides (Locate Variable f)
         , Follow (Locate Literal f) f ~ Literal 
         , FromSides (Locate Literal f)
         , Follow (Locate Literal t) t ~ Literal 
         , FromSides (Locate Literal t)
         , MonadError String m
         ) => Literals m f t where
    literals1 changed (VariantF (tag :: SSide ss) res) = 
        case ( proveFollowInsert @ss @Not @t 
             , proveFollowInsert @ss @Variable @t
             , proveFollowInsert @ss @Not @(Insert Variable t) 
             ) of 
             ( HRefl, HRefl, HRefl) ->
               -- ^ we have now proved that the ss references the same constructor in f and t
               case testEquality tag (fromSides @(Locate Not f)) of
                  Just Refl -> 
                  -- ^ we now have a proof that the node is a Not so we can match it out
                    case res of
                       Not expr@(Pure (Molecule (VariantF (tagv :: SSide ssv) resv))) -> 
                         case ( proveFollowInsert @ssv @Not @t 
                              , proveFollowInsert @ssv @Literal @t
                              , proveFollowInsert @ssv @Not @(Insert Variable t) 
                              ) of 
                              ( HRefl, HRefl, HRefl) ->
                              -- ^ we have now proved that the ssv references the same constructor in f and t
                                case testEquality tagv (fromSides @(Locate Literal t)) of
                                   Just Refl -> 
                                     -- ^ we have now have a proof that resv is a Literal so we can match it out
                                     case resv of
                                       Positive (Name v) -> do
                                         writeSTRef changed True
                                         pure (iNegLiteral v)
                                         -- ^ we can make a literal in negative context now
                                       _ -> lift $ throwError $ "literals1: Not is applied to a Negative Literal. There should be no double negation by now. \n" 
                                                    ++ Pretty.render (pPrint expr)
--                                   Nothing -> pureVNode $ VariantF tag res -- TODO try this, it should not type check it t does not contain Not
                                   Nothing -> lift $ throwError $ "literals1: Not is applied to something that is not a Literal. \n" 
                                                    ++ Pretty.render (pPrint expr)
                                   -- ^ we fail here since t will not be a Molecule that contains Not Atoms 
                  Nothing ->
                    case testEquality tag (fromSides @(Locate Variable f)) of
                       Just Refl -> do
                       -- ^ we have now have a proof that resv is a Variable so we can match it out
                         case res of
                           Variable v -> do
                             writeSTRef changed True
                             pure (iPosLiteral v)
                             -- ^ we can make a literal in positive context now 
                       Nothing -> pureVNode $ VariantF tag res
                       -- ^ this is some other Atom we don't care about
    literals molecule = runSTT $ do
        changed <- newSTRef False
        res <- foldMoleculeM (literals1 changed) molecule
        cha <- readSTRef changed
        return (cha, res)


