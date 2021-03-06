{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
-- | Types with meta-variables

module Lamdu.Infer.Meta
    ( Final(..), _Unbound, _Bound
    , Link(..), _LinkFinal, _Link
    , MetaVarInfo(..)
    , MetaVar, MetaTypeAST(..), MetaType, MetaComposite
    ) where

import           Control.DeepSeq (NFData(..))
import qualified Control.Lens as Lens
import qualified Data.RefZone as RefZone
import qualified Lamdu.Expr.Type as Type
import           Lamdu.Expr.Type.Constraints (Constraints)
import           Lamdu.Expr.Type.Tag (ASTTag(..), IsTag(..))
import           Lamdu.Infer.Scope.Skolems (SkolemScope)
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

import           Prelude.Compat

data MetaVarInfo tag = MetaVarInfo
   { metaVarConstraints :: Constraints tag
   , metaVarSkolemScope :: SkolemScope
   }

instance IsTag tag => Semigroup (MetaVarInfo tag) where
    {-# INLINE (<>) #-}
    MetaVarInfo x0 y0 <> MetaVarInfo x1 y1 =
        MetaVarInfo (x0 <> x1) (y0 <> y1)

instance IsTag tag => Monoid (MetaVarInfo tag) where
    {-# INLINE mempty #-}
    mempty = MetaVarInfo mempty mempty
    mappend = (<>)

data Final tag
    = Unbound (MetaVarInfo tag)
    | Bound (Type.AST tag MetaTypeAST)

data Link tag
    = LinkFinal (Final tag)
    | Link (MetaVar tag)

type MetaVar tag = RefZone.Ref (Link tag)

-- | Type.AST fixpoint that adds meta-variables
data MetaTypeAST tag
    = MetaTypeVar {-# UNPACK #-}!(MetaVar tag)
    | MetaTypeAST !(Type.AST tag MetaTypeAST)
instance NFData (MetaTypeAST tag) where
    rnf (MetaTypeVar x) = rnf x
    rnf (MetaTypeAST x) = rnf x
instance Pretty (MetaTypeAST tag) where
    pPrint (MetaTypeVar pos) = pPrint pos
    pPrint (MetaTypeAST t) = pPrint t

Lens.makePrisms ''Link
Lens.makePrisms ''Final

type MetaType = MetaTypeAST 'TypeT
type MetaComposite c = MetaTypeAST ('CompositeT c)
