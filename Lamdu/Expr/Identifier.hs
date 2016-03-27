{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Lamdu.Expr.Identifier
    ( Identifier(..)
    , Tag(..)
    , NominalId(..), TParamId(..)
    ) where

import           Control.DeepSeq (NFData(..))
import           Data.String (IsString)
import           Data.Text (Text)
import qualified Data.Text as Text
import           Lamdu.Expr.Type.Tag (ASTTag)
import           Text.PrettyPrint (text)
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

import           Prelude.Compat

newtype NominalId = NominalId { _nominalId :: Identifier }
    deriving (Eq, Ord, Show, NFData, IsString, Pretty)

newtype TParamId (tag :: ASTTag) = TParamId { _tParamId :: Identifier }
    deriving (Eq, Ord, Show, NFData, IsString, Pretty)

newtype Identifier = Identifier { _identifierText :: Text }
    deriving (Eq, Ord, Show, NFData, IsString)
instance Pretty Identifier where pPrint = text . Text.unpack . _identifierText

newtype Tag = Tag { _tag :: Identifier }
    deriving (Eq, Ord, Show, NFData, IsString, Pretty)
