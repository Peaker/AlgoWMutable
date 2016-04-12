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
import           Lamdu.Expr.Type.Tag (ASTTag(..), IsTag)
import           Lamdu.Infer.Meta (MetaType, MetaTypeAST(..), MetaVarInfo(..))
import qualified Lamdu.Infer.Monad as M
import           Lamdu.Infer.Scope.Skolems (SkolemScope)
import           Text.PrettyPrint ((<+>))
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

import           Prelude.Compat

instantiateFromNom ::
    SkolemScope -> NominalId -> Nominal ->
    M.Infer s (Map (TParamId 'TypeT) MetaType, MetaType)
instantiateFromNom = nonOpaque (instantiate M.freshMetaVar)

-- ToNom Monad:

data MEnv s = MEnv
    { mEnvBinders :: {-# UNPACK #-}!(STRef s SchemeBinders)
    , mEnvInfer :: !(M.Env s)
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

type ReplaceSkolem m =
    forall tag. IsTag tag => MetaVarInfo tag -> m (MetaTypeAST tag)

freshSkolem :: ReplaceSkolem (M s)
freshSkolem (MetaVarInfo constraints _) =
    do
        name <- liftInfer M.freshTVarName
        let binders = schemeBindersSingleton name constraints
        M.askEnv <&> mEnvBinders
            >>= M.liftST . (`modifySTRef` mappend binders)
        Type.TSkolem name & MetaTypeAST & return

-- ToNom:

instantiateToNom ::
    SkolemScope -> NominalId -> Nominal ->
    M.Infer s (Map (TParamId 'TypeT) MetaType, (SchemeBinders, MetaType))
instantiateToNom = nonOpaque instantiateSkolems

-- Rename all the skolems to fresh names
instantiateSkolems ::
    SkolemScope -> Map (TParamId 'TypeT) MetaType -> NominalScheme ->
    M.Infer s (SchemeBinders, MetaType)
instantiateSkolems skolemScope tParams nominalScheme =
    instantiate freshSkolem skolemScope tParams nominalScheme & runM

nonOpaque ::
    (SkolemScope -> Map (TParamId 'TypeT) MetaType -> NominalScheme -> M.Infer s a) ->
    SkolemScope -> NominalId -> Nominal -> M.Infer s (Map (TParamId 'TypeT) MetaType, a)
nonOpaque _ _ name (Nominal _ OpaqueNominal) = M.OpaqueNominalUsed name & M.throwError
nonOpaque f skolemScope _ (Nominal params (NominalType scheme)) =
    do
        tParams <- params & Map.fromSet (const (M.freshMetaVar info)) & sequenceA
        innerType <- f skolemScope tParams scheme
        return (tParams, innerType)
    where
        info = MetaVarInfo TypeConstraints skolemScope

instantiate ::
    Monad m =>
    ReplaceSkolem m -> SkolemScope -> Map (TParamId 'TypeT) MetaType ->
    NominalScheme -> m MetaType
instantiate replaceSkolem skolemScope tParams (NominalScheme binders typ) =
    M.instantiateBinders (replaceSkolem . info) binders typ $ \go -> \case
    ParameterizedType t -> go t
    ParamRef pId ->
        Map.lookup pId tParams
        & maybe (error (show missingMsg)) return
        where
            missingMsg =
                "ParamRef" <+> pPrint pId <+> "missing in" <+>
                pPrint (Map.keys tParams)
    where
        info :: Constraints tag -> MetaVarInfo tag
        info = MetaVarInfo ?? skolemScope
