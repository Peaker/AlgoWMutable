{-# LANGUAGE NoImplicitPrelude, OverloadedStrings #-}
{-# OPTIONS -fno-warn-orphans #-}
module MapPretty (pPrintWith) where

import Prelude.Compat

import Data.Map
import Text.PrettyPrint.HughesPJClass

instance (Pretty k, Pretty v) => Pretty (Map k v) where
    pPrint = pPrintWith pPrint pPrint

pPrintWith :: (k -> Doc) -> (a -> Doc) -> Map k a -> Doc
pPrintWith key val m =
    "{" <>
    (nest 2 . vcat) [key k <> ":" <+> val v | (k, v) <- toList m]
    <> "}"
