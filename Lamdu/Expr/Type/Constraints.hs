{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoImplicitPrelude #-}
module Lamdu.Expr.Type.Constraints
    ( Constraints(..)
    ) where

import           Control.DeepSeq (NFData(..))
import           Data.Semigroup (Semigroup(..))
import           Data.Set (Set)
import           Lamdu.Expr.Identifier (Tag)
import           Lamdu.Expr.Type.Tag

import           Prelude

data Constraints tag where
    TypeConstraints :: Constraints 'TypeT
    -- forbidden field set:
    CompositeConstraints :: !(Set Tag) -> Constraints ('CompositeT c)

instance Eq (Constraints tag) where
    (==) a b =
        case a of
        TypeConstraints ->
            case b :: Constraints 'TypeT of
            TypeConstraints -> True
        CompositeConstraints x ->
            -- GADT exhaustiveness checking, ugh!
            case b :: tag ~ 'CompositeT c => Constraints ('CompositeT c) of
            CompositeConstraints y -> x == y

instance NFData (Constraints tag) where
    rnf TypeConstraints = ()
    rnf (CompositeConstraints cs) = rnf cs

instance IsTag t => Semigroup (Constraints t) where
    TypeConstraints <> TypeConstraints = TypeConstraints
    CompositeConstraints x <> CompositeConstraints y =
        CompositeConstraints (x <> y)

instance IsTag t => Monoid (Constraints t) where
    mempty =
        case tagRefl :: ASTTagEquality t of
        IsTypeT -> TypeConstraints
        IsCompositeT _ -> CompositeConstraints mempty
    mappend x y = x <> y
