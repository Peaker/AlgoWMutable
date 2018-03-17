{-# LANGUAGE NoImplicitPrelude #-}
module Data.Binary.Utils
    ( decodeS, encodeS
    ) where

import           Data.Binary (Binary(..))
import qualified Data.Binary as Binary
import qualified Data.ByteString.Lazy as LBS
import qualified Data.ByteString as SBS

import           Prelude

strictifyBS :: LBS.ByteString -> SBS.ByteString
strictifyBS = SBS.concat . LBS.toChunks

lazifyBS :: SBS.ByteString -> LBS.ByteString
lazifyBS = LBS.fromChunks . pure

decodeS :: Binary a => SBS.ByteString -> a
decodeS = Binary.decode . lazifyBS

encodeS :: Binary a => a -> SBS.ByteString
encodeS = strictifyBS . Binary.encode
