{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Lamdu.Expr.Type.Constraints
    ( Constraints(..)
    ) where

import Control.DeepSeq (NFData(..))
import Data.Set (Set)
import Lamdu.Expr.Identifier (Tag)
import Lamdu.Expr.Type.Tag

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

instance Monoid (Constraints 'TypeT) where
    mempty = TypeConstraints
    mappend _ _ = TypeConstraints

instance Monoid (Constraints ('CompositeT c)) where
    mempty = CompositeConstraints mempty
    mappend (CompositeConstraints x) (CompositeConstraints y) =
        CompositeConstraints (x `mappend` y)
