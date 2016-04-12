{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
module Lamdu.Expr.Type.Nominal
    ( ParameterizedType(..)
    , NominalScheme(..)
    , NominalType(..)
    , Nominal(..)
    ) where

import           Control.DeepSeq (NFData(..))
import           Data.Set (Set)
import           Lamdu.Expr.Identifier (TParamId)
import qualified Lamdu.Expr.Type as Type
import           Lamdu.Expr.Type.Scheme (SchemeBinders)
import           Lamdu.Expr.Type.Tag (ASTTag(..))

import           Prelude.Compat

-- TODO: Replace with ordinary ADT when ParamRef is allowed anywhere
data ParameterizedType tag where
    ParameterizedType :: !(Type.AST tag ParameterizedType) -> ParameterizedType tag
    ParamRef :: {-# UNPACK #-}!(TParamId 'TypeT) -> ParameterizedType 'TypeT
instance NFData (ParameterizedType tag) where
    rnf (ParameterizedType ast) = rnf ast
    rnf (ParamRef paramId) = rnf paramId

data NominalScheme = NominalScheme
    { nominalSchemeBinders :: {-# UNPACK #-}!SchemeBinders
    , nominalSchemeType :: !(ParameterizedType 'TypeT)
    }
instance NFData NominalScheme where
    rnf (NominalScheme a b) = rnf a `seq` rnf b

data NominalType = OpaqueNominal | NominalType NominalScheme
instance NFData NominalType where
    rnf OpaqueNominal = ()
    rnf (NominalType pType) = rnf pType

data Nominal = Nominal
    { nParams :: Set (TParamId 'TypeT)
    , nType :: NominalType
    }
instance NFData Nominal where
    rnf (Nominal a b) = rnf a `seq` rnf b
