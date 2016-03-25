{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Type
    ( TId(..), TParamId(..)
    , Type, Composite
    , TypeAST(..)
      , _TFun, _TInst, _TRecord, _TSum
      , _TEmptyComposite, _TCompositeExtend
    , ntraverse
    , SchemeBinders(..)
    , Scheme(..), forAll

    , T(..), TVarName(..)

    , recordType, compositeFrom, (~>), tInst
    , intType, boolType
    ) where

import           Control.DeepSeq (NFData(..))
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Proxy (Proxy(..))
import qualified Data.Set as Set
import           Data.String (IsString)
import           Identifier (Identifier(..), Tag(..))
import           MapPretty ()
import           PrettyUtils ((<+?>), intercalate)
import           Text.PrettyPrint (Doc, (<+>), (<>), text)
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)
import           Type.Constraints (Constraints(..))
import           Type.Tag
    ( ASTTag(..), IsCompositeTag(..), CompositeTagEquality(..)
    , RecordT, SumT )

import           Prelude.Compat

newtype TVarName (tag :: ASTTag) = TVarName { _tVarName :: Int }
    deriving (Eq, Ord, Show, Pretty, NFData)

newtype TId = TId { _tid :: Identifier }
    deriving (Eq, Ord, Show, NFData, IsString, Pretty)

newtype TParamId = TParamId { _tParamId :: Identifier }
    deriving (Eq, Ord, Show, NFData, IsString, Pretty)

data TypeAST tag ast where
    TFun :: !(ast 'TypeT) -> !(ast 'TypeT) -> TypeAST 'TypeT ast
    TInst :: {-# UNPACK #-}!TId -> !(Map TParamId (ast 'TypeT)) -> TypeAST 'TypeT ast
    TRecord :: !(ast RecordT) -> TypeAST 'TypeT ast
    TSum :: !(ast SumT) -> TypeAST 'TypeT ast
    TEmptyComposite :: IsCompositeTag c => TypeAST ('CompositeT c) ast
    TCompositeExtend ::
        IsCompositeTag c => {-# UNPACK #-}!Tag -> !(ast 'TypeT) ->
        !(ast ('CompositeT c)) -> TypeAST ('CompositeT c) ast

type Type = TypeAST 'TypeT
type Composite c = TypeAST ('CompositeT c)

instance (NFData (ast 'TypeT),
          NFData (ast RecordT),
          NFData (ast SumT),
          NFData (ast tag)) =>
         NFData (TypeAST tag ast) where
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
    TypeAST tag ast -> f (TypeAST tag ast')
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

_TFun :: Lens.Prism' (TypeAST 'TypeT ast) (ast 'TypeT, ast 'TypeT)
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

_TEmptyComposite :: IsCompositeTag c => Lens.Prism' (TypeAST ('CompositeT c) ast) ()
_TEmptyComposite = Lens.prism' (\() -> TEmptyComposite) $ \case
    TEmptyComposite -> Just ()
    _ -> Nothing

_TCompositeExtend ::
    IsCompositeTag c =>
    Lens.Prism' (TypeAST ('CompositeT c) ast)
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

data T tag
    = T (TypeAST tag T)
    -- HACK: When skolems are properly supported, they'll be qualified
    -- vars inside the TypeAST itself
    | TVar (TVarName tag)
instance NFData (T tag) where
    rnf (T x) = rnf x
    rnf (TVar x) = rnf x

instance Pretty (TypeAST tag T) => Pretty (T tag) where
    pPrintPrec level prec (T typ) = pPrintPrec level prec typ
    pPrintPrec _ _ (TVar name) = text "a" <> pPrint name

infixr 4 ~>
(~>) :: T 'TypeT -> T 'TypeT -> T 'TypeT
a ~> b = T $ TFun a b

compositeFrom :: IsCompositeTag c => [(Tag, T 'TypeT)] -> T ('CompositeT c)
compositeFrom [] = T TEmptyComposite
compositeFrom ((name, typ):fs) = T $ TCompositeExtend name typ $ compositeFrom fs

recordType :: [(Tag, T 'TypeT)] -> T 'TypeT
recordType = T . TRecord . compositeFrom

tInst :: TId -> Map TParamId (T 'TypeT) -> T 'TypeT
tInst name params = T $ TInst name params

intType :: T 'TypeT
intType = tInst "Int" Map.empty

boolType :: T 'TypeT
boolType = tInst "Bool" Map.empty

type TVarBinders tag = Map (TVarName tag) (Constraints tag)

data SchemeBinders = SchemeBinders
    { schemeTypeBinders :: TVarBinders 'TypeT
    , schemeRecordBinders :: TVarBinders RecordT
    , schemeSumBinders :: TVarBinders SumT
    }
instance NFData SchemeBinders where
    rnf (SchemeBinders x y z) = rnf x `seq` rnf y `seq` rnf z
instance Monoid SchemeBinders where
    mempty = SchemeBinders Map.empty Map.empty Map.empty
    mappend (SchemeBinders t0 r0 s0) (SchemeBinders t1 r1 s1)
        | enableAssertions =
            SchemeBinders
            -- TODO: Can use assert-same-constraints and compile out for
            -- perf instead of mappend
            (Map.unionWith assertSameConstraints t0 t1)
            (Map.unionWith assertSameConstraints r0 r1)
            (Map.unionWith assertSameConstraints s0 s1)
        | otherwise =
            SchemeBinders
            (Map.union t0 t1)
            (Map.union r0 r1)
            (Map.union s0 s1)
        where
            enableAssertions = False
            assertSameConstraints x y
                | x == y = x
                | otherwise =
                  "Differing constraints of same " ++
                  "unification variable encountered"
                  & error

nullBinders :: SchemeBinders -> Bool
nullBinders (SchemeBinders a b c) = Map.null a && Map.null b && Map.null c

data Scheme tag = Scheme
    { schemeBinders :: SchemeBinders
    , schemeType :: T tag
    }
instance NFData (Scheme tag) where
    rnf (Scheme x y) = rnf x `seq` rnf y

pPrintTV :: (TVarName tag, Constraints tag) -> Doc
pPrintTV (tv, constraints) =
    "∀a" <> pPrint tv <> suffix constraints
    where
        suffix :: Constraints tag -> Doc
        suffix TypeConstraints = ""
        suffix (CompositeConstraints cs) =
            "∉" <> (intercalate " " . map pPrint) (Set.toList cs)

instance Pretty SchemeBinders where
    pPrint (SchemeBinders tvs rtvs stvs) =
        intercalate " " $
        map pPrintTV (Map.toList tvs) ++
        map pPrintTV (Map.toList rtvs) ++
        map pPrintTV (Map.toList stvs)

instance Pretty (TypeAST tag T) => Pretty (Scheme tag) where
    pPrint (Scheme binders typ)
        | nullBinders binders = pPrint typ
        | otherwise = pPrint binders <> "." <+?> pPrint typ

forAll ::
    Int -> Int -> Int ->
    ([T 'TypeT] -> [T RecordT] -> [T SumT] -> T tag) ->
    Scheme tag
forAll nTvs nRtvs nStvs mkType =
    Scheme (SchemeBinders cTvs cRtvs cStvs) $
    mkType (map TVar tvs) (map TVar rtvs) (map TVar stvs)
    where
        cTvs = Map.fromList [ (tv, mempty) | tv <- tvs ]
        cRtvs = Map.fromList [ (tv, mempty) | tv <- rtvs ]
        cStvs = Map.fromList [ (tv, mempty) | tv <- stvs ]
        tvs = map TVarName [1..nTvs]
        rtvs = map TVarName [nTvs+1..nTvs+nRtvs]
        stvs = map TVarName [nTvs+nRtvs+1..nTvs+nRtvs+nStvs]
