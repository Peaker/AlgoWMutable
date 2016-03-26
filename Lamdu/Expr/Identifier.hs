{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Lamdu.Expr.Identifier
    ( Identifier(..)
    , Tag(..)
    ) where

import           Control.DeepSeq (NFData(..))
import           Data.String (IsString)
import           Data.Text (Text)
import qualified Data.Text as Text
import           Text.PrettyPrint (text)
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

import           Prelude.Compat

newtype Identifier = Identifier { _identifierText :: Text }
    deriving (Eq, Ord, Show, NFData, IsString)
instance Pretty Identifier where pPrint = text . Text.unpack . _identifierText

newtype Tag = Tag { _tag :: Identifier }
    deriving (Eq, Ord, Show, NFData, IsString, Pretty)
