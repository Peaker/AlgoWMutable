-- | Phantom type-level tags for types & composites
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE DataKinds #-}
module Lamdu.Expr.Type.Tag
    ( CompositeTag(..), CompositeTagEquality(..), IsCompositeTag(..)
    , RecordT
    , SumT
    , ASTTag(..), ASTTagEquality(..), IsTag(..)
    ) where

import           Data.Proxy (Proxy(..))
import           Pretty.Map ()

import           Prelude.Compat

data CompositeTag = RecordC | SumC
data ASTTag = TypeT | CompositeT CompositeTag
type RecordT = 'CompositeT 'RecordC
type SumT = 'CompositeT 'SumC

data CompositeTagEquality c where
    IsRecordC :: CompositeTagEquality 'RecordC
    IsSumC :: CompositeTagEquality 'SumC

data ASTTagEquality t where
    IsTypeT :: ASTTagEquality 'TypeT
    IsCompositeT :: !(CompositeTagEquality c) -> ASTTagEquality ('CompositeT c)

class IsCompositeTag t where
    compositeTagRefl :: CompositeTagEquality t
    compositeChar :: Proxy t -> Char
instance IsCompositeTag 'RecordC where
    compositeTagRefl = IsRecordC
    compositeChar _ = '*'
instance IsCompositeTag 'SumC where
    compositeTagRefl = IsSumC
    compositeChar _ = '+'

class IsTag t where tagRefl :: ASTTagEquality t
instance IsTag 'TypeT where tagRefl = IsTypeT
instance IsCompositeTag c => IsTag ('CompositeT c) where
    tagRefl = IsCompositeT compositeTagRefl
