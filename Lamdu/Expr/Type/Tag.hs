-- | Phantom type-level tags for types & composites
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
module Lamdu.Expr.Type.Tag
    ( CompositeTag(..), CompositeTagEquality(..), IsCompositeTag(..)
    , RecordT
    , VariantT
    , ASTTag(..), ASTTagEquality(..), IsTag(..)
    ) where

import           Data.Proxy (Proxy(..))
import           Pretty.Map ()

import           Prelude.Compat

data CompositeTag = RecordC | VariantC
data ASTTag = TypeT | CompositeT CompositeTag
type RecordT = 'CompositeT 'RecordC
type VariantT = 'CompositeT 'VariantC

data CompositeTagEquality c where
    IsRecordC :: CompositeTagEquality 'RecordC
    IsVariantC :: CompositeTagEquality 'VariantC

data ASTTagEquality t where
    IsTypeT :: ASTTagEquality 'TypeT
    IsCompositeT :: !(CompositeTagEquality c) -> ASTTagEquality ('CompositeT c)

class IsCompositeTag t where
    compositeTagRefl :: CompositeTagEquality t
    compositeChar :: Proxy t -> Char
instance IsCompositeTag 'RecordC where
    compositeTagRefl = IsRecordC
    compositeChar _ = '*'
instance IsCompositeTag 'VariantC where
    compositeTagRefl = IsVariantC
    compositeChar _ = '+'

class IsTag t where tagRefl :: ASTTagEquality t
instance IsTag 'TypeT where tagRefl = IsTypeT
instance IsCompositeTag c => IsTag ('CompositeT c) where
    tagRefl = IsCompositeT compositeTagRefl
