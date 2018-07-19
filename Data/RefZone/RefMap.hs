{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE NoImplicitPrelude, GeneralizedNewtypeDeriving, TemplateHaskell #-}
module Data.RefZone.RefMap
    ( RefMap, at
    ) where

import           Control.Lens (LensLike')
import qualified Control.Lens as Lens
import           Data.IntMap (IntMap)
import           Data.RefZone.Internal

import           Prelude.Compat

newtype RefMap v = RefMap { _refMap :: IntMap v }
     deriving (Eq, Ord, Semigroup, Monoid)
Lens.makeLenses ''RefMap

at :: Functor f => Ref a -> LensLike' f (RefMap v) (Maybe v)
at (Ref key) = refMap . Lens.at key
