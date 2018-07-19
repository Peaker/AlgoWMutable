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
    , freshRefWith
    , readRef, writeRef
    , freshMetaVar
    , extendSkolemScope
    , lookupSkolem
    , lookupNominal
    , Unwrap
    , instantiate, instantiateBinders
    ) where


import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.ST (ST)
import           Control.Monad.Trans.State.Strict (StateT(..))
import           Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import           Data.RefZone (Zone)
import qualified Data.RefZone as RefZone
import           Data.STRef
import           Lamdu.Expr.Identifier (Tag(..), NominalId(..))
import qualified Lamdu.Expr.Type as Type
import           Lamdu.Expr.Type.Constraints (Constraints(..))
import           Lamdu.Expr.Type.Nominal (Nominal)
import           Lamdu.Expr.Type.Pure (T(..))
import           Lamdu.Expr.Type.Scheme (Scheme(..), SchemeBinders(..), schemeBindersLookup)
import           Lamdu.Expr.Type.Tag
    ( ASTTagEquality(..), IsTag(..), CompositeTagEquality(..) )
import           Lamdu.Expr.Val (Var)
import           Lamdu.Infer.Meta
    ( MetaVar, MetaTypeAST(..), Link(..), Final(..), MetaVarInfo(..) )
import           Lamdu.Infer.Scope (Scope)
import qualified Lamdu.Infer.Scope as Scope
import           Lamdu.Infer.Scope.Skolems
    ( SkolemScope, SkolemScopeId(..), skolemScopeBinders )
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
    { envFresh :: {-# UNPACK #-}!(STRef s Int)
    , envZone :: {-# UNPACK #-}!(Zone s)
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
    { _inferFresh :: {-# UNPACK #-}!Int
    , _inferFrozen :: {-# UNPACK #-}!RefZone.Frozen
    }

emptyContext :: Context
emptyContext = Context 0 RefZone.emptyFrozen

runInfer ::
    (forall s. Infer s a) ->
    StateT Context (Either Err) a
runInfer act =
    StateT $ \(Context freshNum frozen) ->
    let ZonedInferResult res =
            RefZone.freeze $ do
                fresh <- newSTRef freshNum
                zone <- RefZone.clone frozen
                eRes <-
                    unInfer act Env { envFresh = fresh, envZone = zone }
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

{-# INLINE lookupNominal #-}
lookupNominal :: NominalId -> Scope -> Infer s Nominal
lookupNominal n scope =
    Scope.lookupNominal n scope
    & maybe (throwError (NominalNotInScope n)) return

{-# INLINE lookupSkolem #-}
lookupSkolem :: IsTag tag => Type.TVarName tag -> SkolemScope -> Infer s (Constraints tag)
lookupSkolem v scope =
    skolemScopeBinders scope
    & schemeBindersLookup v
    & maybe (throwError (SkolemNotInScope (pPrint v))) return

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

extendSkolemScope :: SchemeBinders -> Scope -> Infer s Scope
extendSkolemScope binders scope =
    do
        freshId <- nextFresh <&> SkolemScopeId
        Scope.extendSkolemScope freshId binders scope & return

{-# INLINE freshMetaVar #-}
freshMetaVar :: MetaVarInfo tag -> Infer s (MetaTypeAST tag)
freshMetaVar info = freshRefWith info <&> MetaTypeVar

type Unwrap m f =
    forall tag. IsTag tag =>
    ((Type.AST tag f -> m (MetaTypeAST tag)) ->
     f tag -> m (MetaTypeAST tag))

-- | Convert a Scheme's bound/quantified variables to meta-variables
instantiateBinders ::
    forall m f tag. (Monad m, IsTag tag) =>
    (forall tag'. IsTag tag' => Constraints tag' -> m (MetaTypeAST tag')) ->
    SchemeBinders -> f tag -> Unwrap m f -> m (MetaTypeAST tag)
instantiateBinders replaceSkolem (SchemeBinders typeVars recordVars variantVars) typ unwrap =
    {-# SCC "instantiate" #-}
    do
        typeUFs    <- {-# SCC "instantiate.freshtvs"  #-}traverse replaceSkolem typeVars
        recordUFs  <- {-# SCC "instantiate.freshrtvs" #-}traverse replaceSkolem recordVars
        variantUFs <- {-# SCC "instantiate.freshstvs" #-}traverse replaceSkolem variantVars
        let go :: IntMap (MetaTypeAST t) -> Type.AST t f -> m (MetaTypeAST t)
            go binders (Type.TSkolem (Type.TVarName i)) = return (binders IntMap.! i)
            go _ typeAST =
                Type.ntraverse
                (unwrap (go typeUFs))
                (unwrap (go recordUFs))
                (unwrap (go variantUFs)) typeAST <&> MetaTypeAST
        let goTop =
                case tagRefl :: ASTTagEquality tag of
                IsTypeT -> go typeUFs
                IsCompositeT IsRecordC -> go recordUFs
                IsCompositeT IsVariantC -> go variantUFs
        unwrap goTop typ

-- | Convert a Scheme's bound/quantified variables to meta-variables
instantiate :: IsTag tag => Scheme tag -> SkolemScope -> Infer s (MetaTypeAST tag)
instantiate (Scheme binders typ) skolemScope =
    instantiateBinders (freshMetaVar . (`MetaVarInfo` skolemScope)) binders typ (. unT)

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

freshTVarName :: Infer s (Type.TVarName tag)
freshTVarName = nextFresh <&> Type.TVarName
