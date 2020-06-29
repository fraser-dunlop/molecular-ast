{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Molecule.PureInfer where
import Atoms.Elements.Name
import Atoms.Elements.Variable
import Atoms.Molecule.AST
import Atoms.Molecule.HasTypeConstraints
import Atoms.Molecule.InferScope
import Atoms.Molecule.PureInferState
import Atoms.Molecule.RTraversable
import Atoms.Molecule.ScopeTypes
import Atoms.Molecule.Types
import Atoms.Molecule.TypeError
import Atoms.Molecule.ZipMatchable
import qualified Control.Lens as Lens
import Control.Lens.Operators
import Control.Monad.Except (MonadError(..))
import Control.Monad.Reader (MonadReader(..))
import Control.Monad.RWS
import Control.Monad.State (MonadState(..))
import Data.Functor.Identity
import qualified Data.Map as Map
import Hyper
import Hyper.Infer
import Hyper.Class.Infer.Env
import Hyper.Infer.ScopeLevel
import Hyper.Recurse
import Hyper.Type.AST.Nominal
import Hyper.Type.AST.Scheme
import Hyper.Type.AST.Var
import Hyper.Unify
import Hyper.Unify.Apply
import Hyper.Unify.Binding
import Hyper.Unify.Generalize
import Hyper.Unify.QuantifiedVar
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF


newtype PureInfer g a =
    PureInfer
    ( RWST (InferScope g UVar) () (PureInferState g)
        (Either (TypeError g # Pure)) a
    )
    deriving newtype
    ( Functor, Applicative, Monad
    , MonadError (TypeError g # Pure)
    , MonadReader (InferScope g UVar)
    , MonadState (PureInferState g)
    )

Lens.makePrisms ''PureInfer

execPureInfer :: (ForAllIn Functor g) => PureInfer g a
              -> Either (TypeError g # Pure) a
execPureInfer act =
    runRWST (act ^. _PureInfer) emptyInferScope emptyPureInferState
    <&> (^. Lens._1)

inferExpr ::
    forall m g.
    ( HasF Variable g
    , ForAllIn Functor g 
    , Follow (Locate Variable g) g ~ Variable
    , FromSides (Locate Variable g)
    , HasInferredType (Molecule (VariantF g))
    , Infer m (Molecule (VariantF g))
    , HasScheme (Types g) m (TypeOf (Molecule (VariantF g)))
    , RTraversable (Molecule (VariantF g))
    , RTraversableInferOf (Molecule (VariantF g))
    ) =>
    Pure # (Molecule (VariantF g)) ->
    m (Pure # Scheme (Types g) (TypeOf (Molecule (VariantF g))))
inferExpr x =
    do
        inferRes <- infer (wrap (const (Ann (Const ()))) x)
        result <-
            inferRes ^# hAnn . Lens._2 . _InferResult . inferredType (Proxy @(Molecule (VariantF g)))
            & generalize
            >>= saveScheme
        result <$
            htraverse_
            ( Proxy @(Infer m) #*# Proxy @RTraversableInferOf #*#
                \w (Const () :*: InferResult i) ->
                withDict (inferContext (Proxy @m) w) $
                htraverse_ (Proxy @(UnifyGen m) #> void . applyBindings) i
            ) (_HFlip # inferRes)


--withEnv ::
--    ( UnifyGen m (Molecule (VariantF g)), MonadReader env m
--    , HasScheme (Molecule (VariantF g)) m (Types g) 
--    ) =>
--    Lens.LensLike' Lens.Identity env (InferScope g (UVarOf m)) -> m a -> m a
--withEnv l act =
--    do
--        ret <- loadScheme returnScheme
--        let addEnv x =
--                x
--                & varSchemes . _ScopeTypes . Lens.at "return" ?~ MkHFlip ret
--        local (l %~ addEnv) act
--
--returnScheme :: Pure # Scheme (Types g) (Molecule (VariantF g)) 
--returnScheme =
--    forAll (Lens.Identity "value") (Lens.Identity "effects") $
--    \(Lens.Identity val) _ -> TFunP val mutType
--
--forAll ::
--    (Traversable t, Traversable u) =>
--    t Name -> u Name ->
--    (t (h # (Molecule (VariantF g))) -> h # (Molecule (VariantF g))) ->
--    Pure # Scheme (Types g) (Molecule (VariantF g))
--forAll tvs rvs body =
--    _Pure #
--    Scheme (Types (foralls tvs) (foralls rvs))
--    (body (tvs <&> TVarP) (rvs <&> RVarP) ^. hPlain)
--    where
--        foralls ::
--            ( Foldable f
--            , QVar typ ~ Name
--            , Monoid (TypeConstraintsOf typ)
--            ) =>
--            f Name -> QVars # typ
--        foralls xs =
--            xs ^.. Lens.folded <&> (, mempty)
--            & Map.fromList & QVars


type instance UVarOf (PureInfer g) = UVar


--instance MonadNominals Name (Molecule (VariantF g)) (PureInfer g) where
--    getNominalDecl name = Lens.view nominals <&> (^?! Lens.ix name)

instance HasScope (PureInfer g) (ScopeTypes g) where
    getScope = Lens.view varSchemes

instance LocalScopeType Name (UVar # (Molecule (VariantF g))) (PureInfer g) where
    localScopeType h v = local (varSchemes . _ScopeTypes . Lens.at h ?~ MkHFlip (GMono v))

instance LocalScopeType Name (GTerm UVar # (Molecule (VariantF g))) (PureInfer g) where
    localScopeType h v = local (varSchemes . _ScopeTypes . Lens.at h ?~ MkHFlip v)

instance MonadScopeLevel (PureInfer g) where
    localLevel = local (scopeLevel . _ScopeLevel +~ 1)



instance ( HasF Variable g
         , ForAllIn Functor g 
         , Follow (Locate Variable g) g ~ Variable
         , FromSides (Locate Variable g)
         ) => HasQuantifiedVar (Molecule (VariantF g)) where
    type QVar (Molecule (VariantF g)) = Name 
    quantifiedVar = qVarPrism 


instance MonadQuantify ScopeLevel Name (PureInfer g) where
    newQuantifiedVariable _ =
        pisFreshQVars . tTyp . Lens._Wrapped <<+= 1 <&> Name . ('t':) . show

instance ( ForAllIn Traversable g
         , ForAllIn Foldable g
         , ForAllIn Functor g
         , ForAllIn (HasTypeConstraints1 g) g
         , ForAllIn (ZipMatchable1 g) g
         , HasF Variable g 
         , Follow (Locate Variable g) g ~ Variable
         , FromSides (Locate Variable g)
         ) => UnifyGen (PureInfer g) (Molecule (VariantF g)) where
    scopeConstraints _ = Lens.view scopeLevel



instance ( ForAllIn Traversable g
         , ForAllIn Foldable g
         , ForAllIn Functor g
         , ForAllIn (HasTypeConstraints1 g) g
         , ForAllIn (ZipMatchable1 g) g
         , HasF Variable g 
         , Follow (Locate Variable g) g ~ Variable
         , FromSides (Locate Variable g)
         ) => Unify (PureInfer g) (Molecule (VariantF g)) where
    binding = bindingDict (pisBindings . tTyp)
    unifyError e =
        htraverse (Proxy @(Unify (PureInfer g)) #> applyBindings) e
        >>= throwError . TypError

instance ( ForAllIn Traversable g
         , ForAllIn Foldable g
         , ForAllIn Functor g
         , ForAllIn (HasTypeConstraints1 g) g
         , ForAllIn (ZipMatchable1 g) g
         , HasF Variable g 
         , Follow (Locate Variable g) g ~ Variable
         , FromSides (Locate Variable g)
         ) => HasScheme (Types g) (PureInfer g) (Molecule (VariantF g)) 



