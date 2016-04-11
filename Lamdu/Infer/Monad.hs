{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
module Lamdu.Infer.Monad
    ( InferEnv
    , Env, localEnv, askEnv
    , Infer
    , Err(..), throwError
    , Context, emptyContext
    , runInfer
    , repr
    , liftST
    , freshTVarName
    , freshRef, freshRefWith
    , readRef, writeRef
    , freshMetaVar
    , localScope
    , withSkolemScope
    , lookupSkolem
    , lookupGlobal, lookupLocal, lookupNominal
    , ReplaceSkolem, Unwrap
    , instantiate, instantiateBinders
    , generalize, deref, runDeref
    ) where

import           Control.Lens (Lens')
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Lens.Tuple
import           Control.Monad (when)
import           Control.Monad.ST (ST)
import           Control.Monad.Trans.State.Strict (StateT(..))
import           Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import           Data.Monoid ((<>))
import           Data.RefZone (Zone)
import qualified Data.RefZone as RefZone
import           Data.RefZone.RefMap (RefMap)
import qualified Data.RefZone.RefMap as RefMap
import           Data.RefZone.RefSet (RefSet)
import qualified Data.RefZone.RefSet as RefSet
import           Data.STRef
import           Lamdu.Expr.Identifier (Tag(..), NominalId(..))
import qualified Lamdu.Expr.Type as Type
import           Lamdu.Expr.Type.Constraints (Constraints(..))
import           Lamdu.Expr.Type.Nominal (Nominal)
import           Lamdu.Expr.Type.Pure (T(..))
import           Lamdu.Expr.Type.Scheme (Scheme(..), SchemeBinders(..), schemeBindersSingleton)
import           Lamdu.Expr.Type.Tag
    ( ASTTag(..), ASTTagEquality(..), IsTag(..)
    , CompositeTagEquality(..), RecordT, SumT )
import           Lamdu.Expr.Val (Var)
import           Lamdu.Infer.Meta
    ( MetaType, MetaVar, MetaTypeAST(..), Link(..), Final(..), MetaVarInfo(..) )
import           Lamdu.Infer.Scope (Scope)
import qualified Lamdu.Infer.Scope as Scope
import           Lamdu.Infer.Scope.Skolems (SkolemScopeId(..))
import           Pretty.Map ()
import           Pretty.Utils (intercalate)
import           Text.PrettyPrint (Doc, (<+>))
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

import           Prelude.Compat

data Err
    = DoesNotUnify Doc Doc
    | VarNotInScope Var
    | SkolemNotInScope Doc
    | SkolemEscapes Doc
    | OpaqueNominalUsed NominalId
    | NominalWrongParams NominalId Doc Doc
    | NominalNotInScope NominalId
    | InfiniteType
    | DuplicateFields [Tag]
    | ConstraintUnavailable Tag Doc
    deriving (Show)

instance Pretty Err where
    pPrint (DoesNotUnify expected got) =
        "expected:" <+> expected <+> "but got:" <+> got
    pPrint (OpaqueNominalUsed name) =
        pPrint name <+> "used but is opaque!"
    pPrint (NominalWrongParams name expected given) =
        pPrint name <+> "expects params:" <+> expected <+> "but given:" <+> given
    pPrint (NominalNotInScope name) =
        pPrint name <+> "not in scope!"
    pPrint (VarNotInScope name) =
        pPrint name <+> "not in scope!"
    pPrint (SkolemNotInScope name) =
        name <+> "not in scope!"
    pPrint (SkolemEscapes name) =
        name <+> "escapes its scope (value is not polymorphic enough)!"
    pPrint InfiniteType =
        "Infinite type encountered"
    pPrint (DuplicateFields names) =
        "Duplicate tags in composite:" <+>
        (intercalate ", " . map pPrint) names
    pPrint (ConstraintUnavailable tag skolem) =
        "Constraints unavailable:" <+> pPrint tag <+> skolem

data Env s = Env
    { envFresh :: STRef s Int
    , envZone :: Zone s
    , envScope :: Scope MetaType
    }

newtype InferEnv env s a = Infer
    { unInfer :: env -> ST s (Either Err a)
    } deriving (Functor)
type Infer s = InferEnv (Env s) s
instance Applicative (InferEnv env s) where
    {-# INLINE pure #-}
    pure x = Infer $ \_ -> pure (Right x)
    {-# INLINE (<*>) #-}
    Infer f <*> Infer x =
        Infer $ \s -> f s >>= \case
        Left err -> pure (Left err)
        Right fres -> x s >>= \case
            Left err -> pure (Left err)
            Right xres ->
                pure (Right (fres xres))
instance Monad (InferEnv env s) where
    {-# INLINE return #-}
    return = pure
    {-# INLINE (>>=) #-}
    Infer act >>= f = Infer $ \s -> act s >>= \case
        Left err -> pure (Left err)
        Right x -> unInfer (f x) s

newtype ZonedInferResult a b = ZonedInferResult (Either Err (a, b))
    deriving (Functor, Foldable, Traversable)

data Context = Context
    { _inferFresh :: !Int
    , _inferFrozen :: !RefZone.Frozen
    }

emptyContext :: Context
emptyContext = Context 0 RefZone.emptyFrozen

runInfer ::
    Scope MetaType -> (forall s. Infer s a) ->
    StateT Context (Either Err) a
runInfer scope act =
    StateT $ \(Context freshNum frozen) ->
    let ZonedInferResult res =
            RefZone.freeze $ do
                fresh <- newSTRef freshNum
                zone <- RefZone.clone frozen
                eRes <- unInfer act Env { envFresh = fresh, envZone = zone, envScope = scope }
                newFresh <- readSTRef fresh
                eRes
                    & Lens._Right %~ (\r -> ((newFresh, r), zone))
                    & ZonedInferResult
                    & return
    in  res & Lens._Right %~
        \((freshNum', res'), frozen') ->
        (res', Context freshNum' frozen')

{-# INLINE askEnv #-}
askEnv :: InferEnv env s env
askEnv = Infer (return . Right)

{-# INLINE liftST #-}
liftST :: ST s a -> InferEnv env s a
liftST act = Infer $ \_ -> act <&> Right

throwError :: Err -> InferEnv env s a
throwError err = Infer $ \_ -> return $ Left err

{-# INLINE localEnv #-}
localEnv :: (b -> a) -> InferEnv a s x -> InferEnv b s x
localEnv f (Infer act) = Infer (act . f)

{-# INLINE newRef #-}
newRef :: a -> Infer s (RefZone.Ref a)
newRef x =
    do
        zone <- askEnv <&> envZone
        RefZone.newRef zone x & liftST

readRef :: RefZone.Ref b -> Infer s b
readRef ref =
    do
        zone <- askEnv <&> envZone
        RefZone.readRef zone ref & liftST

{-# INLINE writeRef #-}
writeRef :: RefZone.Ref a -> a -> Infer s ()
writeRef ref val =
    do
        zone <- askEnv <&> envZone
        RefZone.writeRef zone ref val & liftST

{-# INLINE localScope #-}
localScope ::
    (Scope MetaType -> Scope MetaType) ->
    Infer s a -> Infer s a
localScope f = localEnv $ \e -> e { envScope = f (envScope e) }

{-# INLINE askScope #-}
askScope :: Infer s (Scope MetaType)
askScope = askEnv <&> envScope

{-# INLINE lookupNominal #-}
lookupNominal :: NominalId -> Infer s Nominal
lookupNominal n =
    askScope <&> Scope.lookupNominal n
    >>= maybe (throwError (NominalNotInScope n)) return

{-# INLINE lookupSkolem #-}
lookupSkolem :: IsTag tag => Type.TVarName tag -> Infer s (Constraints tag)
lookupSkolem v =
    askScope <&> Scope.lookupSkolem v
    >>= maybe (throwError (SkolemNotInScope (pPrint v))) return

{-# INLINE lookupLocal #-}
lookupLocal :: Var -> Infer s (Maybe MetaType)
lookupLocal v = askScope <&> Scope.lookupLocal v

{-# INLINE lookupGlobal #-}
lookupGlobal :: Var -> Infer s (Maybe (Scheme 'TypeT))
lookupGlobal v = askScope <&> Scope.lookupGlobal v

nextFresh :: Infer s Int
nextFresh =
    askEnv <&> envFresh >>= \ref ->
    do
        old <- readSTRef ref
        let !new = 1 + old
        writeSTRef ref $! new
        return new
    & liftST

{-# INLINE freshRefWith #-}
freshRefWith :: MetaVarInfo tag -> Infer s (MetaVar tag)
freshRefWith = newRef . LinkFinal . Unbound

{-# INLINE freshRef #-}
freshRef :: Constraints tag -> Infer s (MetaVar tag)
freshRef cs =
    do
        skolemScope <- askScope <&> Scope.skolemScope
        MetaVarInfo cs skolemScope & freshRefWith

withSkolemScope :: SchemeBinders -> Infer s a -> Infer s a
withSkolemScope binders act =
    do
        freshId <- nextFresh <&> SkolemScopeId
        localScope (Scope.extendSkolemScope freshId binders) act

{-# INLINE freshMetaVar #-}
freshMetaVar :: Constraints tag -> Infer s (MetaTypeAST tag)
freshMetaVar cs = freshRef cs <&> MetaTypeVar

type ReplaceSkolem m =
    forall tag. IsTag tag => Constraints tag -> m (MetaTypeAST tag)

type Unwrap m f =
    forall tag. IsTag tag =>
    ((Type.AST tag f -> m (MetaTypeAST tag)) ->
     f tag -> m (MetaTypeAST tag))

-- | Convert a Scheme's bound/quantified variables to meta-variables
instantiateBinders ::
    forall m f tag. (Monad m, IsTag tag) =>
    ReplaceSkolem m -> SchemeBinders -> f tag ->
    Unwrap m f -> m (MetaTypeAST tag)
instantiateBinders replaceSkolem (SchemeBinders typeVars recordVars sumVars) typ unwrap =
    {-# SCC "instantiate" #-}
    do
        typeUFs   <- {-# SCC "instantiate.freshtvs"  #-}traverse replaceSkolem typeVars
        recordUFs <- {-# SCC "instantiate.freshrtvs" #-}traverse replaceSkolem recordVars
        sumUFs    <- {-# SCC "instantiate.freshstvs" #-}traverse replaceSkolem sumVars
        let go :: IntMap (MetaTypeAST t) -> Type.AST t f -> m (MetaTypeAST t)
            go binders (Type.TSkolem (Type.TVarName i)) = return (binders IntMap.! i)
            go _ typeAST =
                Type.ntraverse
                (unwrap (go typeUFs))
                (unwrap (go recordUFs))
                (unwrap (go sumUFs)) typeAST <&> MetaTypeAST
        let goTop =
                case tagRefl :: ASTTagEquality tag of
                IsTypeT -> go typeUFs
                IsCompositeT IsRecordC -> go recordUFs
                IsCompositeT IsSumC -> go sumUFs
        unwrap goTop typ

-- | Convert a Scheme's bound/quantified variables to meta-variables
instantiate :: IsTag tag => Scheme tag -> Infer s (MetaTypeAST tag)
instantiate (Scheme binders typ) = instantiateBinders freshMetaVar binders typ (. unT)

repr :: MetaVar tag -> Infer s (MetaVar tag, Final tag)
repr x =
    do
        zone <- askEnv <&> envZone
        let go ref =
                RefZone.readRef zone ref >>= \case
                LinkFinal final -> return (ref, final)
                Link innerRef ->
                    do
                        (preFinal, final) <- go innerRef
                        -- path compression:
                        -- Point to the pre-final link, so that the
                        -- Final isn't copied but shared.
                        RefZone.writeRef zone ref (Link preFinal)
                        return (preFinal, final)
        liftST $ go x

type DerefCache = (RefMap (T 'TypeT), RefMap (T RecordT), RefMap (T SumT))
data DerefEnv s = DerefEnv
    { _derefEnvVisited :: RefSet
    , derefEnvCache :: STRef s DerefCache
    , derefEnvBinders :: STRef s SchemeBinders
    , derefEnvInfer :: Env s
    }
type Deref s = InferEnv (DerefEnv s) s

Lens.makeLenses ''DerefEnv

derefInfer :: Infer s a -> Deref s a
derefInfer = localEnv derefEnvInfer

derefCache :: forall tag. IsTag tag => RefZone.Ref (Link tag) -> Lens' DerefCache (Maybe (T tag))
derefCache tag =
    ( case (tagRefl :: ASTTagEquality tag) of
      IsTypeT                -> _1
      IsCompositeT IsRecordC -> _2
      IsCompositeT IsSumC    -> _3
    ) . RefMap.at tag

derefMemoize ::
    IsTag tag => RefZone.Ref (Link tag) -> Deref s (T tag) -> Deref s (T tag)
derefMemoize ref act =
    do
        cacheRef <- askEnv <&> derefEnvCache
        liftST (readSTRef cacheRef) <&> (^. derefCache ref)
            >>= \case
            Just t -> pure t
            Nothing ->
                do
                    res <- act
                    derefCache ref ?~ res & modifySTRef cacheRef & liftST
                    return res

freshTVarName :: Infer s (Type.TVarName tag)
freshTVarName = nextFresh <&> Type.TVarName

derefVar :: IsTag tag => MetaVar tag -> Deref s (T tag)
derefVar var =
    do
        (ref, final) <- repr var & derefInfer
        visited <- askEnv <&> _derefEnvVisited
        when (ref `RefSet.isMember` visited) $ throwError InfiniteType
        derefMemoize ref $
            case final of
            Bound ast -> derefAST ast & localEnv (derefEnvVisited %~ RefSet.insert ref)
            Unbound info ->
                do
                    tvName <- derefInfer freshTVarName
                    askEnv
                        <&> derefEnvBinders
                        >>= liftST . flip modifySTRef
                            (schemeBindersSingleton tvName (metaVarConstraints info) <>)
                    return $ T $ Type.TSkolem tvName

deref :: IsTag tag => MetaTypeAST tag -> Deref s (T tag)
deref = \case
    MetaTypeAST ast -> derefAST ast
    MetaTypeVar var -> derefVar var

derefAST :: IsTag tag => Type.AST tag MetaTypeAST -> Deref s (T tag)
derefAST = fmap T . Type.ntraverse deref deref deref

{-# INLINE runDeref #-}
runDeref :: Deref s a -> Infer s a
runDeref = fmap snd . runDerefWith

runDerefWith :: Deref s a -> Infer s (SchemeBinders, a)
runDerefWith act =
    do
        cacheRef <- newSTRef mempty & liftST
        bindersRef <- newSTRef mempty & liftST
        res <- localEnv (DerefEnv mempty cacheRef bindersRef) act
        binders <- readSTRef bindersRef & liftST
        return (binders, res)

-- | Convert a meta-type's meta-variables to a scheme with quantified
-- variables
generalize :: IsTag tag => MetaTypeAST tag -> Infer s (Scheme tag)
generalize t =
    {-# SCC "generalize" #-}
    do
        (binders, typ) <- deref t & runDerefWith
        Scheme binders typ & return
