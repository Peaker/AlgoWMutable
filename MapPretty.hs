{-# OPTIONS -fno-warn-orphans #-}
module MapPretty () where

import Prelude.Compat

import Data.Map
import Text.PrettyPrint.HughesPJClass

instance (Pretty k, Pretty v) => Pretty (Map k v) where
    pPrint m =
        "{" <>
        (nest 2 . vcat) [pPrint k <> ":" <+> pPrint v | (k, v) <- toList m]
        <> "}"

