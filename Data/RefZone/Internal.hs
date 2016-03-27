{-# LANGUAGE RankNTypes, NoImplicitPrelude, GeneralizedNewtypeDeriving #-}
-- | Internal types of the RefZone/RefSet/Ref

module Data.RefZone.Internal
    ( Ref(..)
    ) where

import           Control.DeepSeq (NFData(..))
import           Text.PrettyPrint (text, (<>))
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

import           Prelude.Compat

newtype Ref a = Ref Int deriving (Eq, Ord, NFData)

instance Pretty (Ref a) where pPrint (Ref i) = text "R" <> pPrint i
