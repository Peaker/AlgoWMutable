{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}
module Lamdu.Expr.Type.Pure
    ( T(..)
    , recordType, compositeFrom, (~>), tInst
    ) where

import           Control.DeepSeq (NFData(..))
import           Data.Map.Strict (Map)
import           Lamdu.Expr.Identifier (Tag, NominalId, TParamId)
import qualified Lamdu.Expr.Type as Type
import           Lamdu.Expr.Type.Tag (ASTTag(..), IsCompositeTag(..))
import           Pretty.Map ()
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

import           Prelude.Compat

newtype T tag = T { unT :: Type.AST tag T }
instance NFData (T tag) where rnf (T x) = rnf x

instance Pretty (Type.AST tag T) => Pretty (T tag) where
    pPrintPrec level prec (T typ) = pPrintPrec level prec typ

infixr 4 ~>
(~>) :: T 'TypeT -> T 'TypeT -> T 'TypeT
a ~> b = T $ Type.TFun a b

compositeFrom :: IsCompositeTag c => [(Tag, T 'TypeT)] -> T ('CompositeT c)
compositeFrom [] = T Type.TEmptyComposite
compositeFrom ((name, typ):fs) = T $ Type.TCompositeExtend name typ $ compositeFrom fs

recordType :: [(Tag, T 'TypeT)] -> T 'TypeT
recordType = T . Type.TRecord . compositeFrom

tInst :: NominalId -> Map (TParamId 'TypeT) (T 'TypeT) -> T 'TypeT
tInst name params = T $ Type.TInst name params

