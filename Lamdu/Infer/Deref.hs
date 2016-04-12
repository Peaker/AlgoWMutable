-- | Dereference meta-asts
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
module Lamdu.Infer.Deref
    ( Deref, run
    , deref, generalize
    ) where

import           Control.Lens (Lens')
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Lens.Tuple
import           Control.Monad (when)
import           Data.Monoid ((<>))
import qualified Data.RefZone as RefZone
import           Data.RefZone.RefMap (RefMap)
import qualified Data.RefZone.RefMap as RefMap
import           Data.RefZone.RefSet (RefSet)
import qualified Data.RefZone.RefSet as RefSet
import           Data.STRef
import qualified Lamdu.Expr.Type as Type
import           Lamdu.Expr.Type.Pure (T(..))
import           Lamdu.Expr.Type.Scheme (Scheme(..), SchemeBinders(..), schemeBindersSingleton)
import           Lamdu.Expr.Type.Tag
    ( ASTTag(..), ASTTagEquality(..), IsTag(..)
    , CompositeTagEquality(..), RecordT, SumT )
import           Lamdu.Infer.Meta
    ( MetaVar, MetaTypeAST(..), Link(..), Final(..), MetaVarInfo(..) )
import qualified Lamdu.Infer.Monad as M

import           Prelude.Compat

type DerefCache = (RefMap (T 'TypeT), RefMap (T RecordT), RefMap (T SumT))
data DerefEnv s = DerefEnv
    { _derefEnvVisited :: RefSet
    , derefEnvCache :: STRef s DerefCache
    , derefEnvBinders :: STRef s SchemeBinders
    , derefEnvInfer :: M.Env s
    }
type Deref s = M.InferEnv (DerefEnv s) s

Lens.makeLenses ''DerefEnv

derefInfer :: M.Infer s a -> Deref s a
derefInfer = M.localEnv derefEnvInfer

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
        cacheRef <- M.askEnv <&> derefEnvCache
        M.liftST (readSTRef cacheRef) <&> (^. derefCache ref)
            >>= \case
            Just t -> pure t
            Nothing ->
                do
                    res <- act
                    derefCache ref ?~ res & modifySTRef cacheRef & M.liftST
                    return res

derefVar :: IsTag tag => MetaVar tag -> Deref s (T tag)
derefVar var =
    do
        (ref, final) <- M.repr var & derefInfer
        visited <- M.askEnv <&> _derefEnvVisited
        when (ref `RefSet.isMember` visited) $ M.throwError M.InfiniteType
        derefMemoize ref $
            case final of
            Bound ast -> derefAST ast & M.localEnv (derefEnvVisited %~ RefSet.insert ref)
            Unbound info ->
                do
                    tvName <- derefInfer M.freshTVarName
                    M.askEnv
                        <&> derefEnvBinders
                        >>= M.liftST . flip modifySTRef
                            (schemeBindersSingleton tvName (metaVarConstraints info) <>)
                    return $ T $ Type.TSkolem tvName

deref :: IsTag tag => MetaTypeAST tag -> Deref s (T tag)
deref = \case
    MetaTypeAST ast -> derefAST ast
    MetaTypeVar var -> derefVar var

derefAST :: IsTag tag => Type.AST tag MetaTypeAST -> Deref s (T tag)
derefAST = fmap T . Type.ntraverse deref deref deref

runWith :: Deref s a -> M.Infer s (SchemeBinders, a)
runWith act =
    do
        cacheRef <- newSTRef mempty & M.liftST
        bindersRef <- newSTRef mempty & M.liftST
        res <- M.localEnv (DerefEnv mempty cacheRef bindersRef) act
        binders <- readSTRef bindersRef & M.liftST
        return (binders, res)

{-# INLINE run #-}
run :: Deref s a -> M.Infer s a
run = fmap snd . runWith

-- | Convert a meta-type's meta-variables to a scheme with quantified
-- variables
generalize :: IsTag tag => MetaTypeAST tag -> M.Infer s (Scheme tag)
generalize t =
    {-# SCC "generalize" #-}
    do
        (binders, typ) <- deref t & runWith
        Scheme binders typ & return
