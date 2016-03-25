{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
module Type
    ( TId(..), TParamId(..)
    , Type, Composite
    , AST(..)
      , _TFun, _TInst, _TRecord, _TSum
      , _TEmptyComposite, _TCompositeExtend
    , ntraverse
    ) where

import           Control.DeepSeq (NFData(..))
import qualified Control.Lens as Lens
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Proxy (Proxy(..))
import           Data.String (IsString)
import           Identifier (Identifier(..), Tag(..))
import           MapPretty ()
import           PrettyUtils ((<+?>))
import           Text.PrettyPrint ((<+>), text)
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)
import           Type.Tag
    ( ASTTag(..), IsCompositeTag(..), CompositeTagEquality(..)
    , RecordT, SumT )

import           Prelude.Compat

newtype TId = TId { _tid :: Identifier }
    deriving (Eq, Ord, Show, NFData, IsString, Pretty)

newtype TParamId = TParamId { _tParamId :: Identifier }
    deriving (Eq, Ord, Show, NFData, IsString, Pretty)

data AST tag ast where
    TFun :: !(ast 'TypeT) -> !(ast 'TypeT) -> AST 'TypeT ast
    TInst :: {-# UNPACK #-}!TId -> !(Map TParamId (ast 'TypeT)) -> AST 'TypeT ast
    TRecord :: !(ast RecordT) -> AST 'TypeT ast
    TSum :: !(ast SumT) -> AST 'TypeT ast
    TEmptyComposite :: IsCompositeTag c => AST ('CompositeT c) ast
    TCompositeExtend ::
        IsCompositeTag c => {-# UNPACK #-}!Tag -> !(ast 'TypeT) ->
        !(ast ('CompositeT c)) -> AST ('CompositeT c) ast

type Type = AST 'TypeT
type Composite c = AST ('CompositeT c)

instance (NFData (ast 'TypeT),
          NFData (ast RecordT),
          NFData (ast SumT),
          NFData (ast tag)) =>
         NFData (AST tag ast) where
    rnf (TFun x y) = rnf x `seq` rnf y
    rnf (TInst n params) = rnf n `seq` rnf params
    rnf (TRecord record) = rnf record
    rnf (TSum s) = rnf s
    rnf TEmptyComposite = ()
    rnf (TCompositeExtend n t r) = rnf n `seq` rnf t `seq` rnf r

{-# INLINE ntraverse #-}
ntraverse ::
    Applicative f =>
    (ast 'TypeT -> f (ast' 'TypeT)) ->
    (ast RecordT -> f (ast' RecordT)) ->
    (ast SumT -> f (ast' SumT)) ->
    AST tag ast -> f (AST tag ast')
ntraverse onTypes onRecords onSums = \case
    TFun a b -> TFun <$> onTypes a <*> onTypes b
    TInst n params -> TInst n <$> traverse onTypes params
    TRecord r -> TRecord <$> onRecords r
    TSum s -> TSum <$> onSums s
    TEmptyComposite -> pure TEmptyComposite
    TCompositeExtend n t (r :: ast ('CompositeT c)) ->
        TCompositeExtend n <$> onTypes t <*>
        case compositeTagRefl :: CompositeTagEquality c of
        IsRecordC -> onRecords r
        IsSumC -> onSums r

_TFun :: Lens.Prism' (AST 'TypeT ast) (ast 'TypeT, ast 'TypeT)
_TFun = Lens.prism' (uncurry TFun) $ \case
    TFun x y -> Just (x, y)
    _ -> Nothing

_TInst :: Lens.Prism' (Type ast) (TId, Map TParamId (ast 'TypeT))
_TInst = Lens.prism' (uncurry TInst) $ \case
    TInst n p -> Just (n, p)
    _ -> Nothing

_TRecord :: Lens.Prism' (Type ast) (ast RecordT)
_TRecord = Lens.prism' TRecord $ \case
    TRecord n -> Just n
    _ -> Nothing

_TSum :: Lens.Prism' (Type ast) (ast SumT)
_TSum = Lens.prism' TSum $ \case
    TSum n -> Just n
    _ -> Nothing

_TEmptyComposite :: IsCompositeTag c => Lens.Prism' (AST ('CompositeT c) ast) ()
_TEmptyComposite = Lens.prism' (\() -> TEmptyComposite) $ \case
    TEmptyComposite -> Just ()
    _ -> Nothing

_TCompositeExtend ::
    IsCompositeTag c =>
    Lens.Prism' (AST ('CompositeT c) ast)
    (Tag, ast 'TypeT, ast ('CompositeT c))
_TCompositeExtend = Lens.prism' (\(n, t, r) -> TCompositeExtend n t r) $ \case
    TCompositeExtend n t r -> Just (n, t, r)
    _ -> Nothing

instance (Pretty (ast 'TypeT),
          Pretty (ast RecordT),
          Pretty (ast SumT)) =>
         Pretty (Type ast) where
    pPrintPrec level prec ast =
        case ast of
        TFun a b ->
            maybeParens (prec > 0) $
            pPrintPrec level 1 a <+> "->" <+?> pPrintPrec level 0 b
        TInst name params
            | Map.null params -> pPrint name
            | otherwise -> pPrint name <+> pPrint params
        TRecord r -> pPrintPrec level prec r
        TSum s -> pPrintPrec level prec s

instance (IsCompositeTag c,
          Pretty (ast 'TypeT),
          Pretty (ast ('CompositeT c))) =>
         Pretty (Composite c ast) where
    pPrintPrec level prec ast =
        case ast of
        TEmptyComposite -> "{}"
        TCompositeExtend n t r ->
            maybeParens (prec > 1) $
            "{" <+> pPrint n <+> ":" <+> pPrintPrec level 0 t <+> "}" <+?>
            text [compositeChar (Proxy :: Proxy c)] <+> pPrintPrec level 1 r
