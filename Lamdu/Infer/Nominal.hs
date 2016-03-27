-- | Nominal inference routines
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
module Lamdu.Infer.Nominal
    ( instantiateFromNom
    ) where

import           Control.Lens.Operators
import           Data.Map (Map)
import qualified Data.Map as Map
import           Lamdu.Expr.Identifier (NominalId, TParamId)
import           Lamdu.Expr.Type.Constraints (Constraints(..))
import           Lamdu.Expr.Type.Nominal
    ( Nominal(..), NominalType(..), NominalScheme(..), ParameterizedType(..) )
import           Lamdu.Expr.Type.Tag (ASTTag(..))
import           Lamdu.Infer.Meta (MetaType)
import qualified Lamdu.Infer.Monad as M
import           Text.PrettyPrint ((<+>))
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

import           Prelude.Compat

instantiateFromNom :: NominalId -> Nominal -> M.Infer s (Map (TParamId 'TypeT) MetaType, MetaType)
instantiateFromNom name (Nominal _ OpaqueNominal) =
    M.OpaqueNominalUsed name & M.throwError
instantiateFromNom _ (Nominal params (NominalType scheme)) =
    do
        tParams <- params & Map.fromSet (const (M.freshMetaVar TypeConstraints)) & sequenceA

        -- walk the typ once, replacing param-refs with keys from tParams
        -- and skolems with fresh vars
        innerType <-
            M.instantiateBinders binders typ $ \go -> \case
                ParamRef pId ->
                    Map.lookup pId tParams
                    & maybe (error (show missingMsg)) return
                    where
                        missingMsg =
                            "ParamRef" <+> pPrint pId <+> "missing in" <+>
                            pPrint (Map.keys tParams)
                ParameterizedType t -> go t
        return (tParams, innerType)
    where
        NominalScheme binders typ = scheme
