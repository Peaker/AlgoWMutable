{-# LANGUAGE NoImplicitPrelude #-}
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
    , runInfer
    , repr
    , freshRef, freshRefWith
    , readRef, writeRef
    , freshMetaVar
    , localScope
    , lookupSkolem
    , lookupGlobal, lookupLocal
    , instantiate, generalize
    ) where

import           Control.Lens (Lens')
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Lens.Tuple
import           Control.Monad (when)
import           Control.Monad.ST (ST, runST)
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
import           Lamdu.Expr.Identifier (Tag(..))
import qualified Lamdu.Expr.Type as Type
import           Lamdu.Expr.Type.Constraints (Constraints(..))
import           Lamdu.Infer.Meta
    ( MetaType, MetaVar, MetaTypeAST(..), Link(..), Final(..), MetaVarInfo(..) )
import           Lamdu.Expr.Type.Pure (T(..))
import           Lamdu.Expr.Type.Scheme (Scheme(..), SchemeBinders(..))
import           Lamdu.Expr.Type.Tag
    ( ASTTag(..), ASTTagEquality(..), IsTag(..)
    , CompositeTagEquality(..), RecordT, SumT )
import           Lamdu.Expr.Val (Var)
import           Lamdu.Infer.Scope (Scope)
import qualified Lamdu.Infer.Scope as Scope
import           Pretty.Map ()
import           Pretty.Utils (intercalate)
import           Text.PrettyPrint (Doc, (<+>))
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

import           Prelude.Compat

data Err
    = DoesNotUnify Doc Doc
    | VarNotInScope Var
    | SkolemNotInScope Doc
    | InfiniteType
    | DuplicateFields [Tag]
    | ConstraintUnavailable Tag Doc
    deriving (Show)

instance Pretty Err where
    pPrint (DoesNotUnify expected got) =
        "expected:" <+> expected <+> "but got:" <+> got
    pPrint (VarNotInScope name) =
        pPrint name <+> "not in scope!"
    pPrint (SkolemNotInScope name) =
        name <+> "not in scope!"
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

runInfer :: Scope MetaType -> (forall s. Infer s a) -> Either Err a
runInfer scope act =
    runST $
    do
        fresh <- newSTRef 0
        zone <- RefZone.new
        unInfer act Env { envFresh = fresh, envZone = zone, envScope = scope }

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

{-# INLINE lookupSkolem #-}
lookupSkolem :: IsTag tag => Type.TVarName tag -> Infer s (Constraints tag)
lookupSkolem v =
    askScope <&> Scope.lookupSkolem v >>= maybe (throwError (SkolemNotInScope (pPrint v))) return

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
    cs
    -- TODO: skolemScope <- askScope <&> Scope.skolemScope
    & mkInfo
    & freshRefWith
    where
        mkInfo = MetaVarInfo -- TODO: skolemScope

{-# INLINE freshMetaVar #-}
freshMetaVar :: Constraints tag -> Infer s (MetaTypeAST tag)
freshMetaVar cs = freshRef cs <&> MetaTypeVar

-- | Convert a Scheme's bound/quantified variables to meta-variables
instantiate :: forall s tag. IsTag tag => Scheme tag -> Infer s (MetaTypeAST tag)
instantiate (Scheme (SchemeBinders typeVars recordVars sumVars) typ) =
    {-# SCC "instantiate" #-}
    do
        typeUFs <- {-# SCC "instantiate.freshtvs" #-}traverse freshMetaVar typeVars
        recordUFs <- {-# SCC "instantiate.freshrtvs" #-}traverse freshMetaVar recordVars
        sumUFs <- {-# SCC "instantiate.freshstvs" #-}traverse freshMetaVar sumVars
        let go :: IntMap (MetaTypeAST t) -> T t -> Infer s (MetaTypeAST t)
            go binders (T (Type.TSkolem (Type.TVarName i))) = return (binders IntMap.! i)
            go _ (T typeAST) =
                Type.ntraverse (go typeUFs) (go recordUFs) (go sumUFs) typeAST
                <&> MetaTypeAST
        {-# SCC "instantiate.go" #-}typ & case tagRefl :: ASTTagEquality tag of
            IsTypeT -> go typeUFs
            IsCompositeT IsRecordC -> go recordUFs
            IsCompositeT IsSumC -> go sumUFs

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

schemeBindersSingleton :: forall tag. IsTag tag => Type.TVarName tag -> Constraints tag -> SchemeBinders
schemeBindersSingleton (Type.TVarName tvName) cs =
    case tagRefl :: ASTTagEquality tag of
    IsTypeT -> mempty { schemeTypeBinders = binders }
    IsCompositeT IsRecordC -> mempty { schemeRecordBinders = binders }
    IsCompositeT IsSumC -> mempty { schemeSumBinders = binders }
    where
        binders = IntMap.singleton tvName cs

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
                    tvName <- nextFresh <&> Type.TVarName & derefInfer
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

-- | Convert a meta-type's meta-variables to a scheme with quantified
-- variables
generalize :: IsTag tag => MetaTypeAST tag -> Infer s (Scheme tag)
generalize t =
    {-# SCC "generalize" #-}
    do
        cacheRef <- liftST $ newSTRef mempty
        bindersRef <- liftST $ newSTRef mempty
        typ <- deref t & localEnv (DerefEnv mempty cacheRef bindersRef)
        binders <- liftST $ readSTRef bindersRef
        Scheme binders typ & return
