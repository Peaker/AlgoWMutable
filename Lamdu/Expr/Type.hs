{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
module Lamdu.Expr.Type
    ( Type, Composite
    , TVarName(..)
    , AST(..)
      , _TFun, _TInst, _TRecord, _TVariant, _TSkolem
      , _TEmptyComposite, _TCompositeExtend
    , ntraverse, ntraverse_
    ) where

import           Control.DeepSeq (NFData(..))
import qualified Control.Lens as Lens
import           Data.Foldable (traverse_)
import           Data.Map (Map)
import qualified Data.Map.Strict as Map
import           Data.Proxy (Proxy(..))
import           Lamdu.Expr.Identifier (Tag, NominalId, TParamId)
import           Lamdu.Expr.Type.Tag
    ( ASTTag(..), IsCompositeTag(..), CompositeTagEquality(..)
    , RecordT, VariantT )
import           Pretty.Map ()
import           Pretty.Utils ((<+?>))
import           Text.PrettyPrint ((<+>), text)
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

import           Prelude.Compat

newtype TVarName (tag :: ASTTag) = TVarName { _tVarName :: Int }
    deriving (Eq, Ord, Show, NFData)

instance Pretty (TVarName tag) where
    pPrint (TVarName i) = "a" <> pPrint i

data AST (tag :: ASTTag) ast where
    -- | A skolem is a quantified type-variable (from a Scheme binder)
    TSkolem :: {-# UNPACK #-}!(TVarName tag) -> AST tag ast
    TFun :: !(ast 'TypeT) -> !(ast 'TypeT) -> AST 'TypeT ast
    TInst :: {-# UNPACK #-}!NominalId -> !(Map (TParamId 'TypeT) (ast 'TypeT)) -> AST 'TypeT ast
    TRecord :: !(ast RecordT) -> AST 'TypeT ast
    TVariant :: !(ast VariantT) -> AST 'TypeT ast
    TEmptyComposite :: IsCompositeTag c => AST ('CompositeT c) ast
    TCompositeExtend ::
        IsCompositeTag c => {-# UNPACK #-}!Tag -> !(ast 'TypeT) ->
        !(ast ('CompositeT c)) -> AST ('CompositeT c) ast

type Type = AST 'TypeT
type Composite c = AST ('CompositeT c)

instance (NFData (ast 'TypeT),
          NFData (ast RecordT),
          NFData (ast VariantT),
          NFData (ast tag)) =>
         NFData (AST tag ast) where
    rnf (TSkolem name) = rnf name
    rnf (TFun x y) = rnf x `seq` rnf y
    rnf (TInst n params) = rnf n `seq` rnf params
    rnf (TRecord record) = rnf record
    rnf (TVariant s) = rnf s
    rnf TEmptyComposite = ()
    rnf (TCompositeExtend n t r) = rnf n `seq` rnf t `seq` rnf r

{-# INLINE ntraverse #-}
ntraverse ::
    Applicative f =>
    (ast 'TypeT -> f (ast' 'TypeT)) ->
    (ast RecordT -> f (ast' RecordT)) ->
    (ast VariantT -> f (ast' VariantT)) ->
    AST tag ast -> f (AST tag ast')
ntraverse onTypes onRecords onVariants = \case
    TSkolem v -> pure (TSkolem v)
    TFun a b -> TFun <$> onTypes a <*> onTypes b
    TInst n params -> TInst n <$> traverse onTypes params
    TRecord r -> TRecord <$> onRecords r
    TVariant s -> TVariant <$> onVariants s
    TEmptyComposite -> pure TEmptyComposite
    TCompositeExtend n t (r :: ast ('CompositeT c)) ->
        TCompositeExtend n <$> onTypes t <*>
        case compositeTagRefl :: CompositeTagEquality c of
        IsRecordC -> onRecords r
        IsVariantC -> onVariants r

{-# INLINE ntraverse_ #-}
ntraverse_ ::
    Applicative f =>
    (ast 'TypeT -> f ()) ->
    (ast RecordT -> f ()) ->
    (ast VariantT -> f ()) ->
    AST tag ast -> f ()
ntraverse_ onTypes onRecords onVariants = \case
    TSkolem _ -> pure ()
    TEmptyComposite -> pure ()
    TFun a b -> onTypes a *> onTypes b
    TInst _ params -> traverse_ onTypes params
    TRecord r -> onRecords r
    TVariant s -> onVariants s
    TCompositeExtend _ t (r :: ast ('CompositeT c)) ->
        onTypes t *>
        case compositeTagRefl :: CompositeTagEquality c of
        IsRecordC -> onRecords r
        IsVariantC -> onVariants r

{-# INLINE _TFun #-}
_TFun :: Lens.Prism' (AST 'TypeT ast) (ast 'TypeT, ast 'TypeT)
_TFun = Lens.prism' (uncurry TFun) $ \case
    TFun x y -> Just (x, y)
    _ -> Nothing

{-# INLINE _TSkolem #-}
_TSkolem :: Lens.Prism' (AST tag ast) (TVarName tag)
_TSkolem = Lens.prism' TSkolem $ \case
    TSkolem varName -> Just varName
    _ -> Nothing

{-# INLINE _TInst #-}
_TInst :: Lens.Prism' (Type ast) (NominalId, Map (TParamId 'TypeT) (ast 'TypeT))
_TInst = Lens.prism' (uncurry TInst) $ \case
    TInst n p -> Just (n, p)
    _ -> Nothing

{-# INLINE _TRecord #-}
_TRecord :: Lens.Prism' (Type ast) (ast RecordT)
_TRecord = Lens.prism' TRecord $ \case
    TRecord n -> Just n
    _ -> Nothing

{-# INLINE _TVariant #-}
_TVariant :: Lens.Prism' (Type ast) (ast VariantT)
_TVariant = Lens.prism' TVariant $ \case
    TVariant n -> Just n
    _ -> Nothing

{-# INLINE _TEmptyComposite #-}
_TEmptyComposite :: IsCompositeTag c => Lens.Prism' (AST ('CompositeT c) ast) ()
_TEmptyComposite = Lens.prism' (\() -> TEmptyComposite) $ \case
    TEmptyComposite -> Just ()
    _ -> Nothing

{-# INLINE _TCompositeExtend #-}
_TCompositeExtend ::
    IsCompositeTag c =>
    Lens.Prism' (AST ('CompositeT c) ast)
    (Tag, ast 'TypeT, ast ('CompositeT c))
_TCompositeExtend = Lens.prism' (\(n, t, r) -> TCompositeExtend n t r) $ \case
    TCompositeExtend n t r -> Just (n, t, r)
    _ -> Nothing

instance (Pretty (ast 'TypeT),
          Pretty (ast RecordT),
          Pretty (ast VariantT)) =>
         Pretty (AST tag ast) where
    pPrintPrec level prec ast =
        case ast of
        TSkolem (TVarName name) ->
            text "a" <> pPrint name
        TFun a b ->
            maybeParens (prec > 0) $
            pPrintPrec level 1 a <+> "->" <+?> pPrintPrec level 0 b
        TInst name params
            | Map.null params -> pPrint name
            | otherwise -> pPrint name <+> pPrint params
        TRecord r -> pPrintPrec level prec r
        TVariant s -> pPrintPrec level prec s
        TEmptyComposite -> "{}"
        TCompositeExtend n t (r :: ast ('CompositeT c)) ->
            maybeParens (prec > 1) $
            "{" <+> pPrint n <+> ":" <+> pPrintPrec level 0 t <+> "}" <+?>
            text [compositeChar (Proxy :: Proxy c)] <+>
            ( case compositeTagRefl :: CompositeTagEquality c of
              IsRecordC -> pPrintPrec level 1 r
              IsVariantC    -> pPrintPrec level 1 r )
