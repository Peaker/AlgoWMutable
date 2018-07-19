{-# LANGUAGE NoImplicitPrelude, GeneralizedNewtypeDeriving #-}
module Data.RefZone.RefSet
    ( RefSet, singleton, isMember, insert
    ) where

import           Control.Lens.Operators
import           Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import           Data.RefZone.Internal

import           Prelude.Compat

newtype RefSet = RefSet IntSet
     deriving (Eq, Ord, Monoid, Semigroup)

singleton :: Ref a -> RefSet
singleton (Ref x) = IntSet.singleton x & RefSet

isMember :: Ref a -> RefSet -> Bool
Ref x `isMember` RefSet s = x `IntSet.member` s

insert :: Ref a -> RefSet -> RefSet
Ref x `insert` RefSet s = x `IntSet.insert` s & RefSet
