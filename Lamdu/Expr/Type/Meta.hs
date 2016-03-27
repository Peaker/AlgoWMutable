{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TemplateHaskell #-}
-- | Types with meta-variables

module Lamdu.Expr.Type.Meta
    ( IsBound(..), MetaVar(..), MetaTypeAST(..), MetaType, MetaComposite
    ) where

import           Control.DeepSeq (NFData(..))
import qualified Control.Lens as Lens
import           Data.Monoid ((<>))
import qualified Data.RefZone as RefZone
import           Data.Set (Set)
import qualified Data.Set as Set
import qualified Lamdu.Expr.Type as Type
import           Lamdu.Expr.Type.Constraints (Constraints)
import           Lamdu.Expr.Type.Tag (ASTTag(..))
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

import           Prelude.Compat

data IsBound tag bound
    = Unbound (Constraints tag)
    | Bound bound
    deriving (Functor, Foldable, Traversable)
Lens.makePrisms ''IsBound

data MetaVar tag = MetaVar
    { __unificationPosNames :: Set Int
      -- TODO: Remove names, use mutable bit/level instead
    , __unificationPosRef :: RefZone.Ref (IsBound tag (MetaTypeAST tag))
    }

instance NFData (MetaVar tag) where rnf (MetaVar x y) = rnf x `seq` rnf y
instance Pretty (MetaVar tag) where
    pPrint (MetaVar names _) = "?" <> pPrint (Set.toList names)

-- | Type.AST fixpoint that adds meta-variables
data MetaTypeAST tag
    = MetaTypeVar (MetaVar tag)
    | MetaTypeAST (Type.AST tag MetaTypeAST)
instance NFData (MetaTypeAST tag) where
    rnf (MetaTypeVar x) = rnf x
    rnf (MetaTypeAST x) = rnf x
instance Pretty (Type.AST tag MetaTypeAST) => Pretty (MetaTypeAST tag) where
    pPrint (MetaTypeVar pos) = pPrint pos
    pPrint (MetaTypeAST t) = pPrint t

Lens.makeLenses ''MetaVar

type MetaType = MetaTypeAST 'TypeT
type MetaComposite c = MetaTypeAST ('CompositeT c)
