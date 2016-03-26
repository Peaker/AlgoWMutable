-- | Annotated vals
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
module Lamdu.Expr.Val.Annotated (AV(..)) where

import Control.DeepSeq (NFData(..))
import Lamdu.Expr.Val (Val(..))
import Pretty.Map ()
import Text.PrettyPrint (isEmpty, (<>))
import Text.PrettyPrint.HughesPJClass (Pretty(..))

import Prelude.Compat

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

