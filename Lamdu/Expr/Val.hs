-- | Val AST
{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, OverloadedStrings, GeneralizedNewtypeDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module Lamdu.Expr.Val
    ( Leaf(..)
      , _LVar, _LEmptyRecord, _LAbsurd, _LLiteral, _LHole
    , PrimVal(..), primType, primData
    , Body(..)
      , _BLam, _BApp, _BRecExtend, _BCase, _BGetField
      , _BInject, _BFromNom, _BToNom, _BLeaf
    , Apply(..), applyFunc, applyArg
    , GetField(..), getFieldTag, getFieldRecord
    , Inject(..), injectTag, injectVal
    , Case(..), caseTag, caseMatch, caseMismatch
    , Lam(..), lamParamId, lamResult
    , RecExtend(..), recTag, recFieldVal, recRest
    , Nom(..), nomId, nomVal
    , Var(..), var
    ) where

import           Control.DeepSeq (NFData(..))
import qualified Control.Lens as Lens
import           Data.ByteString (ByteString)
import           Data.ByteString.Hex (showHexBytes)
import           Data.String (IsString)
import           Lamdu.Expr.Identifier (Identifier, Tag, NominalId)
import           Pretty.Map ()
import           Pretty.Utils ((<+?>))
import           Text.PrettyPrint (text, ($+$), (<+>), (<>))
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

import           Prelude.Compat

newtype Var = Var { _var :: Identifier }
    deriving (Eq, Ord, Show, NFData, IsString, Pretty)

data PrimVal = PrimVal
    { _primType :: {-# UNPACK #-} !NominalId
    , _primData :: {-# UNPACK #-} !ByteString
    } deriving (Show, Eq, Ord)
instance NFData PrimVal where
    rnf (PrimVal a b) = rnf a `seq` rnf b

instance Pretty PrimVal where
    pPrint (PrimVal nomId bs) = pPrint nomId <> "{" <> text (showHexBytes bs) <> "}"

data Leaf
    = LVar {-# UNPACK #-}!Var
    | LEmptyRecord
    | LAbsurd
    | LLiteral {-# UNPACK #-}!PrimVal
    | LHole
    deriving (Show)
instance NFData Leaf where
    rnf (LVar x) = rnf x
    rnf (LLiteral x) = rnf x
    rnf LEmptyRecord = ()
    rnf LAbsurd = ()
    rnf LHole = ()

instance Pretty Leaf where
    pPrint (LVar x) = pPrint x
    pPrint LEmptyRecord = "{}"
    pPrint LAbsurd = "Absurd"
    pPrint (LLiteral x) = pPrint x
    pPrint LHole = "?"

class Match f where
    match :: (a -> b -> c) -> f a -> f b -> Maybe (f c)

data Apply v = Apply
    { _applyFunc :: !v
    , _applyArg :: !v
    } deriving (Show, Functor, Foldable, Traversable)
instance NFData v => NFData (Apply v) where rnf (Apply a b) = rnf a `seq` rnf b
instance Match Apply where
    match f (Apply f0 a0) (Apply f1 a1) = Just $ Apply (f f0 f1) (f a0 a1)

data GetField v = GetField
    { _getFieldRecord :: !v
    , _getFieldTag :: Tag
    } deriving (Show, Functor, Foldable, Traversable)
instance NFData v => NFData (GetField v) where rnf (GetField a b) = rnf a `seq` rnf b
instance Match GetField where
    match f (GetField r0 t0) (GetField r1 t1)
        | t0 == t1 = Just $ GetField (f r0 r1) t0
        | otherwise = Nothing

data Inject v = Inject
    { _injectTag :: Tag
    , _injectVal :: !v
    } deriving (Show, Functor, Foldable, Traversable)
instance NFData v => NFData (Inject v) where rnf (Inject a b) = rnf a `seq` rnf b
instance Match Inject where
    match f (Inject t0 r0) (Inject t1 r1)
        | t0 == t1 = Just $ Inject t0 (f r0 r1)
        | otherwise = Nothing

data Case v = Case
    { _caseTag :: Tag
    , _caseMatch :: !v
    , _caseMismatch :: !v
    } deriving (Show, Functor, Foldable, Traversable)
instance NFData v => NFData (Case v) where rnf (Case a b c) = rnf a `seq` rnf b `seq` rnf c
instance Match Case where
    match f (Case t0 h0 hr0) (Case t1 h1 hr1)
        | t0 == t1 = Just $ Case t0 (f h0 h1) (f hr0 hr1)
        | otherwise = Nothing

data Lam v = Lam
    { _lamParamId :: Var
    , _lamResult :: !v
    } deriving (Show, Functor, Foldable, Traversable)
instance NFData v => NFData (Lam v) where rnf (Lam a b) = rnf a `seq` rnf b

data RecExtend v = RecExtend
    { _recTag :: Tag
    , _recFieldVal :: !v
    , _recRest :: !v
    } deriving (Show, Functor, Foldable, Traversable)
instance NFData v => NFData (RecExtend v) where rnf (RecExtend a b c) = rnf a `seq` rnf b `seq` rnf c
instance Match RecExtend where
    match f (RecExtend t0 f0 r0) (RecExtend t1 f1 r1)
        | t0 == t1 = Just $ RecExtend t0 (f f0 f1) (f r0 r1)
        | otherwise = Nothing

data Nom v = Nom
    { _nomId :: NominalId
    , _nomVal :: !v
    } deriving (Show, Functor, Foldable, Traversable)
instance NFData v => NFData (Nom v) where rnf (Nom a b) = rnf a `seq` rnf b
instance Match Nom where
    match f (Nom i0 v0) (Nom i1 v1)
        | i0 == i1 = Just $ Nom i0 (f v0 v1)
        | otherwise = Nothing

data Body v
    = BLam       {-# UNPACK #-}!(Lam v)
    | BApp       {-# UNPACK #-}!(Apply v)
    | BRecExtend {-# UNPACK #-}!(RecExtend v)
    | BCase      {-# UNPACK #-}!(Case v)
    | BGetField  {-# UNPACK #-}!(GetField v)
    | BInject    {-# UNPACK #-}!(Inject v)
    | BFromNom   {-# UNPACK #-}!(Nom v)
    | BToNom     {-# UNPACK #-}!(Nom v)
    | BLeaf      !Leaf
    deriving (Show, Functor, Foldable, Traversable)

instance NFData v => NFData (Body v) where
    rnf (BLam x) = rnf x
    rnf (BApp x) = rnf x
    rnf (BRecExtend x) = rnf x
    rnf (BCase x) = rnf x
    rnf (BGetField x) = rnf x
    rnf (BFromNom x) = rnf x
    rnf (BToNom x) = rnf x
    rnf (BInject x) = rnf x
    rnf (BLeaf x) = rnf x

instance Pretty v => Pretty (Body v) where
    pPrintPrec level prec (BLam (Lam name body)) =
        maybeParens (prec > 0) $
        pPrint name <+> "→" <+> pPrintPrec level 0 body
    pPrintPrec level prec (BApp (Apply func arg)) =
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
    pPrintPrec level prec (BToNom (Nom tId val)) =
        maybeParens (prec > 5) $
        pPrint tId <> "«" <> pPrintPrec level 5 val
    pPrintPrec level prec (BFromNom (Nom tId val)) =
        maybeParens (prec > 5) $
        pPrintPrec level 5 val <> "»" <> pPrint tId
    pPrintPrec level prec (BLeaf leaf) = pPrintPrec level prec leaf

Lens.makeLenses ''Var
Lens.makeLenses ''PrimVal
Lens.makeLenses ''Lam
Lens.makeLenses ''Inject
Lens.makeLenses ''GetField
Lens.makeLenses ''Apply
Lens.makeLenses ''Nom
Lens.makeLenses ''RecExtend
Lens.makeLenses ''Case
Lens.makePrisms ''Leaf
Lens.makePrisms ''Body
