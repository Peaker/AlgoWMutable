{-# LANGUAGE OverloadedStrings #-}
-- | Val AST
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
    , V(..), AV(..)
    , lam, lambda, lambdaRecord
    , absurd, case_, cases
    , litInt, hole
    , ($$), ($$:), ($=), ($.), (.$), ($+), ($-)
    , recVal, var, global, infixApp
    ) where

import Control.DeepSeq (NFData(..))
import Data.String (IsString)
import Identifier
import MapPretty ()
import Prelude.Compat hiding (abs, tail)
import Text.PrettyPrint (isEmpty, fcat, Doc, ($+$), (<+>), (<>))
import Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

infixr 2 <+?>
(<+?>) :: Doc -> Doc -> Doc
x <+?> y = fcat [x, " " <> y]

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

newtype V = V (Val V)
    deriving (Show, Pretty)

data AV a = AV
    { aAnnotation :: a
    , aVal :: Val (AV a)
    } deriving (Show, Functor, Foldable, Traversable)
instance Pretty a => Pretty (AV a) where
    pPrintPrec level prec (AV ann v)
        | isEmpty annDoc = pPrintPrec level prec v
        | otherwise =
        "{" <> annDoc <> "}" <>
        pPrintPrec level 10 v
        where
            annDoc = pPrint ann
instance NFData a => NFData (AV a) where
    rnf (AV ann val) = rnf ann `seq` rnf val

lam :: Var -> V -> V
lam name body = V $ BLam $ Abs name body

lambda :: Var -> (V -> V) -> V
lambda name body = lam name $ body $ var $ name

lambdaRecord :: Var -> [Tag] -> ([V] -> V) -> V
lambdaRecord name fields body = lambda name $ \v -> body $ map (v $.) fields

absurd :: V
absurd = V $ BLeaf LAbsurd

case_ :: Tag -> V -> V -> V
case_ name handler restHandlers = V $ BCase $ Case name handler restHandlers

cases :: [(Tag, V)] -> V
cases = foldr (uncurry case_) absurd

litInt :: Int -> V
litInt = V . BLeaf . LInt

hole :: V
hole = V $ BLeaf LHole

infixl 4 $$
($$) :: V -> V -> V
($$) f a = V $ BApp $ App f a

($$:) :: V -> [(Tag, V)] -> V
func $$: fields = func $$ recVal fields

recVal :: [(Tag, V)] -> V
recVal = foldr extend empty
    where
        extend (name, val) rest = V $ BRecExtend (RecExtend name val rest)
        empty = V $ BLeaf LEmptyRecord

($=) :: Tag -> V -> V -> V
(x $= y) z = V $ BRecExtend $ RecExtend x y z

($.) :: V -> Tag -> V
x $. y = V $ BGetField $ GetField x y

(.$) :: Tag -> V -> V
x .$ y = V $ BInject $ Inject x y

var :: Var -> V
var = V . BLeaf . LVar

global :: GlobalId -> V
global = V . BLeaf . LGlobal

infixApp :: GlobalId -> V -> V -> V
infixApp name x y = global name $$: [("l", x), ("r", y)]

($+) :: V -> V -> V
($+) = infixApp "+"

($-) :: V -> V -> V
($-) = infixApp "-"
