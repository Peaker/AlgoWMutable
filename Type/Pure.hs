{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
module Type.Pure
    ( T(..), TVarName(..)
    , recordType, compositeFrom, (~>), tInst
    , intType, boolType
    ) where

import           Control.DeepSeq (NFData(..))
import           Data.Map (Map)
import qualified Data.Map as Map
import           Identifier (Tag(..))
import           Pretty.Map ()
import           Text.PrettyPrint ((<>), text)
import           Text.PrettyPrint.HughesPJClass (Pretty(..))
import qualified Type
import           Type.Tag (ASTTag(..), IsCompositeTag(..))

import           Prelude.Compat

newtype TVarName (tag :: ASTTag) = TVarName { _tVarName :: Int }
    deriving (Eq, Ord, Show, Pretty, NFData)

data T tag
    = T (Type.AST tag T)
    -- HACK: When skolems are properly supported, they'll be qualified
    -- vars inside the Type.AST itself
    | TVar (TVarName tag)
instance NFData (T tag) where
    rnf (T x) = rnf x
    rnf (TVar x) = rnf x

instance Pretty (Type.AST tag T) => Pretty (T tag) where
    pPrintPrec level prec (T typ) = pPrintPrec level prec typ
    pPrintPrec _ _ (TVar name) = text "a" <> pPrint name

infixr 4 ~>
(~>) :: T 'TypeT -> T 'TypeT -> T 'TypeT
a ~> b = T $ Type.TFun a b

compositeFrom :: IsCompositeTag c => [(Tag, T 'TypeT)] -> T ('CompositeT c)
compositeFrom [] = T Type.TEmptyComposite
compositeFrom ((name, typ):fs) = T $ Type.TCompositeExtend name typ $ compositeFrom fs

recordType :: [(Tag, T 'TypeT)] -> T 'TypeT
recordType = T . Type.TRecord . compositeFrom

tInst :: Type.TId -> Map Type.TParamId (T 'TypeT) -> T 'TypeT
tInst name params = T $ Type.TInst name params

intType :: T 'TypeT
intType = tInst "Int" Map.empty

boolType :: T 'TypeT
boolType = tInst "Bool" Map.empty

