{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-}
module Lamdu.Expr.Type.Constraints
    ( Composite(..), forbiddenFields
    , Constraints(..)
    ) where

import           Control.DeepSeq (NFData(..))
import qualified Control.Lens as Lens
import           Data.Semigroup (Semigroup(..))
import           Data.Set (Set)
import qualified Data.Set as Set
import           Lamdu.Expr.Identifier (Tag)
import           Lamdu.Expr.Type.Tag
import           Pretty.Utils (intercalate)
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

import           Prelude

data Constraints tag where
    TypeConstraints :: Constraints 'TypeT
    -- forbidden field set:
    CompositeConstraints :: Composite c -> Constraints ('CompositeT c)

newtype Composite (c :: CompositeTag) = Composite
    { _forbiddenFields :: Set Tag
    } deriving (Semigroup, Monoid, NFData, Eq, Ord, Show)

Lens.makeLenses ''Composite

instance Pretty (Composite c) where
    pPrint (Composite cs) =
        "∉" <> (intercalate " " . map pPrint) (Set.toList cs)

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
