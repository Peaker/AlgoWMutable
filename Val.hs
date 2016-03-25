-- | Val AST
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
module Val
    ( Val(..)
    , GlobalId(..)
    , Leaf(..)
    , Abs(..), Var(..)
    , App(..)
    , RecExtend(..)
    , Case(..)
    , GetField(..)
    , Inject(..)
    ) where

import Control.DeepSeq (NFData(..))
import Data.String (IsString)
import Identifier
import MapPretty ()
import PrettyUtils ((<+?>))
import Text.PrettyPrint (($+$), (<+>), (<>))
import Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

import Prelude.Compat

data Leaf
    = LVar Var
    | LGlobal GlobalId
    | LEmptyRecord
    | LAbsurd
    | LInt Int
    | LHole
    deriving (Show)
instance NFData Leaf where
    rnf (LVar x) = rnf x
    rnf (LGlobal x) = rnf x
    rnf (LInt x) = rnf x
    rnf LEmptyRecord = ()
    rnf LAbsurd = ()
    rnf LHole = ()

instance Pretty Leaf where
    pPrint (LVar x) = pPrint x
    pPrint (LGlobal x) = pPrint x
    pPrint LEmptyRecord = "{}"
    pPrint LAbsurd = "Absurd"
    pPrint (LInt x) = pPrint x
    pPrint LHole = "?"

newtype GlobalId = GlobalId { _globalId :: Identifier }
    deriving (Eq, Ord, Show, NFData, IsString, Pretty)

newtype Var = Var { _var :: Identifier }
    deriving (Eq, Ord, Show, NFData, IsString, Pretty)

data Abs v = Abs Var !v
    deriving (Show, Functor, Foldable, Traversable)
instance NFData v => NFData (Abs v) where rnf (Abs a b) = rnf a `seq` rnf b

data App v = App !v !v
    deriving (Show, Functor, Foldable, Traversable)
instance NFData v => NFData (App v) where rnf (App a b) = rnf a `seq` rnf b

data RecExtend v = RecExtend Tag !v !v
    deriving (Show, Functor, Foldable, Traversable)
instance NFData v => NFData (RecExtend v) where rnf (RecExtend a b c) = rnf a `seq` rnf b `seq` rnf c

data Case v = Case Tag !v !v
    deriving (Show, Functor, Foldable, Traversable)
instance NFData v => NFData (Case v) where rnf (Case a b c) = rnf a `seq` rnf b `seq` rnf c

data GetField v = GetField !v Tag
    deriving (Show, Functor, Foldable, Traversable)
instance NFData v => NFData (GetField v) where rnf (GetField a b) = rnf a `seq` rnf b

data Inject v = Inject Tag !v
    deriving (Show, Functor, Foldable, Traversable)
instance NFData v => NFData (Inject v) where rnf (Inject a b) = rnf a `seq` rnf b

data Val v
    = BLam (Abs v)
    | BApp (App v)
    | BRecExtend (RecExtend v)
    | BCase (Case v)
    | BGetField (GetField v)
    | BInject (Inject v)
    | BLeaf Leaf
    deriving (Show, Functor, Foldable, Traversable)

instance NFData v => NFData (Val v) where
    rnf (BLam x) = rnf x
    rnf (BApp x) = rnf x
    rnf (BRecExtend x) = rnf x
    rnf (BCase x) = rnf x
    rnf (BGetField x) = rnf x
    rnf (BInject x) = rnf x
    rnf (BLeaf x) = rnf x

instance Pretty v => Pretty (Val v) where
    pPrintPrec level prec (BLam (Abs name body)) =
        maybeParens (prec > 0) $
        pPrint name <+> "→" <+> pPrintPrec level 0 body
    pPrintPrec level prec (BApp (App func arg)) =
        maybeParens (prec > 9) $
        pPrintPrec level 9 func <+> pPrintPrec level 10 arg
    pPrintPrec level prec (BRecExtend (RecExtend name val rest)) =
        maybeParens (prec > 7) $
        "{" <> pPrint name <> "="
        <> pPrintPrec level 8 val <> "} *"
        <+?> pPrintPrec level 7 rest
    pPrintPrec level prec (BCase (Case name handler restHandler)) =
        maybeParens (prec > 7) $
        "case" <+> pPrint name <+> "→"
        <+> pPrintPrec level 8 handler $+$
        pPrintPrec level 7 restHandler
    pPrintPrec level prec (BGetField (GetField val name)) =
        maybeParens (prec > 8) $
        pPrintPrec level 8 val <> "." <> pPrint name
    pPrintPrec level prec (BInject (Inject name val)) =
        maybeParens (prec > 8) $
        pPrint name <+> pPrintPrec level 8 val
    pPrintPrec level prec (BLeaf leaf) = pPrintPrec level prec leaf

