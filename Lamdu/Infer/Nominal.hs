{-# LANGUAGE RankNTypes #-}
-- | Nominal inference routines
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
module Lamdu.Infer.Nominal
    ( instantiateFromNom
    , instantiateToNom
    ) where

import           Control.Lens.Operators
import           Data.Map (Map)
import qualified Data.Map.Strict as Map
import           Data.STRef
import           Lamdu.Expr.Identifier (NominalId, TParamId)
import qualified Lamdu.Expr.Type as Type
import           Lamdu.Expr.Type.Constraints (Constraints(..))
import           Lamdu.Expr.Type.Nominal
    ( Nominal(..), NominalType(..), NominalScheme(..), ParameterizedType(..) )
import           Lamdu.Expr.Type.Scheme (SchemeBinders, schemeBindersSingleton)
import           Lamdu.Expr.Type.Tag (ASTTag(..))
import           Lamdu.Infer.Meta (MetaType, MetaTypeAST(..))
import qualified Lamdu.Infer.Monad as M
import           Text.PrettyPrint ((<+>))
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

import           Prelude.Compat

instantiateFromNom ::
    NominalId -> Nominal -> M.Infer s (Map (TParamId 'TypeT) MetaType, MetaType)
instantiateFromNom = nonOpaque (instantiate M.freshMetaVar)

-- ToNom Monad:

data MEnv s = MEnv
    { mEnvBinders :: STRef s SchemeBinders
    , mEnvInfer :: M.Env s
    }

type M s a = M.InferEnv (MEnv s) s a

liftInfer :: M.Infer s a -> M s a
liftInfer = M.localEnv mEnvInfer

runM :: M s a -> M.Infer s (SchemeBinders, a)
runM act =
    do
        bindersRef <- newSTRef mempty & M.liftST
        res <- M.localEnv (MEnv bindersRef) act
        binders <- readSTRef bindersRef & M.liftST
        return (binders, res)

freshSkolem :: M.ReplaceSkolem (M s)
freshSkolem constraints =
    do
        name <- liftInfer M.freshTVarName
        let binders = schemeBindersSingleton name constraints
        M.askEnv <&> mEnvBinders
            >>= M.liftST . (`modifySTRef` mappend binders)
        Type.TSkolem name & MetaTypeAST & return

-- ToNom:

instantiateToNom ::
    NominalId -> Nominal -> M.Infer s (Map (TParamId 'TypeT) MetaType, (SchemeBinders, MetaType))
instantiateToNom = nonOpaque instantiateSkolems

-- Rename all the skolems to fresh names
instantiateSkolems ::
    Map (TParamId 'TypeT) MetaType -> NominalScheme -> M.Infer s (SchemeBinders, MetaType)
instantiateSkolems tParams nominalScheme =
    instantiate freshSkolem tParams nominalScheme & runM

nonOpaque ::
    (Map (TParamId 'TypeT) MetaType -> NominalScheme -> M.Infer s a) ->
    NominalId -> Nominal -> M.Infer s (Map (TParamId 'TypeT) MetaType, a)
nonOpaque _ name (Nominal _ OpaqueNominal) = M.OpaqueNominalUsed name & M.throwError
nonOpaque f _ (Nominal params (NominalType scheme)) =
    do
        tParams <- params & Map.fromSet (const (M.freshMetaVar TypeConstraints)) & sequenceA
        innerType <- f tParams scheme
        return (tParams, innerType)

instantiate ::
    Monad m =>
    M.ReplaceSkolem m -> Map (TParamId 'TypeT) MetaType -> NominalScheme ->
    m MetaType
instantiate replaceSkolem tParams (NominalScheme binders typ) =
    M.instantiateBinders replaceSkolem binders typ $ \go -> \case
    ParameterizedType t -> go t
    ParamRef pId ->
        Map.lookup pId tParams
        & maybe (error (show missingMsg)) return
        where
            missingMsg =
                "ParamRef" <+> pPrint pId <+> "missing in" <+>
                pPrint (Map.keys tParams)
