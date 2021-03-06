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
import           Text.PrettyPrint (text, ($+$), (<+>))
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

data Apply v = Apply
    { _applyFunc :: !v
    , _applyArg :: !v
    } deriving (Show, Functor, Foldable, Traversable)
instance NFData v => NFData (Apply v) where rnf (Apply a b) = rnf a `seq` rnf b

data GetField v = GetField
    { _getFieldRecord :: !v
    , _getFieldTag :: {-# UNPACK #-}!Tag
    } deriving (Show, Functor, Foldable, Traversable)
instance NFData v => NFData (GetField v) where rnf (GetField a b) = rnf a `seq` rnf b

data Inject v = Inject
    { _injectTag :: {-# UNPACK #-}!Tag
    , _injectVal :: !v
    } deriving (Show, Functor, Foldable, Traversable)
instance NFData v => NFData (Inject v) where rnf (Inject a b) = rnf a `seq` rnf b

data Case v = Case
    { _caseTag :: {-# UNPACK #-}!Tag
    , _caseMatch :: !v
    , _caseMismatch :: !v
    } deriving (Show, Functor, Foldable, Traversable)
instance NFData v => NFData (Case v) where rnf (Case a b c) = rnf a `seq` rnf b `seq` rnf c

data Lam v = Lam
    { _lamParamId :: {-# UNPACK #-}!Var
    , _lamResult :: !v
    } deriving (Show, Functor, Foldable, Traversable)
instance NFData v => NFData (Lam v) where rnf (Lam a b) = rnf a `seq` rnf b

data RecExtend v = RecExtend
    { _recTag :: {-# UNPACK #-}!Tag
    , _recFieldVal :: !v
    , _recRest :: !v
    } deriving (Show, Functor, Foldable, Traversable)
instance NFData v => NFData (RecExtend v) where rnf (RecExtend a b c) = rnf a `seq` rnf b `seq` rnf c

data Nom v = Nom
    { _nomId :: {-# UNPACK #-}!NominalId
    , _nomVal :: !v
    } deriving (Show, Functor, Foldable, Traversable)
instance NFData v => NFData (Nom v) where rnf (Nom a b) = rnf a `seq` rnf b

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
