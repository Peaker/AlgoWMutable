{-# LANGUAGE NoImplicitPrelude, OverloadedStrings #-}
{-# OPTIONS -fno-warn-orphans #-}
module Pretty.Map (pPrintWith) where

import           Data.Map
import           Text.PrettyPrint (Doc, vcat, nest, (<+>), (<>))
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

import           Prelude.Compat hiding ((<>))

instance (Pretty k, Pretty v) => Pretty (Map k v) where
    pPrint = pPrintWith pPrint pPrint

pPrintWith :: (k -> Doc) -> (a -> Doc) -> Map k a -> Doc
pPrintWith key val m =
    "{" <>
    (nest 2 . vcat) [key k <> ":" <+> val v | (k, v) <- toList m]
    <> "}"
