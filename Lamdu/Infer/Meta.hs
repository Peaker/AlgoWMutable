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
import           Data.Semigroup (Semigroup)
import qualified Data.Semigroup as Semigroup
import qualified Lamdu.Expr.Type as Type
import           Lamdu.Expr.Type.Constraints (Constraints)
import           Lamdu.Expr.Type.Tag (ASTTag(..), IsTag(..))
import           Lamdu.Infer.Scope.Skolems (SkolemScope)
import           Text.PrettyPrint ((<>), (<+>))
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

import           Prelude.Compat

data MetaVarInfo tag = MetaVarInfo
   { metaVarConstraints :: Constraints tag
   , metaVarSkolemScope :: SkolemScope
   }

instance Pretty (MetaVarInfo tag) where
    pPrint (MetaVarInfo constraints skolems) =
        "Info{" <> pPrint constraints <> pPrint skolems <> "}"

instance IsTag tag => Semigroup (MetaVarInfo tag) where
    {-# INLINE (<>) #-}
    MetaVarInfo x0 y0 <> MetaVarInfo x1 y1 =
        MetaVarInfo (x0 Semigroup.<> x1) (y0 Semigroup.<> y1)

instance IsTag tag => Monoid (MetaVarInfo tag) where
    {-# INLINE mempty #-}
    mempty = MetaVarInfo mempty mempty
    mappend = (Semigroup.<>)

data Final tag
    = Unbound (MetaVarInfo tag)
    | Bound (Type.AST tag MetaTypeAST)

instance Pretty (Final tag) where
    pPrint (Unbound cs) = "(?" <> pPrint cs <> ")"
    pPrint (Bound ast) = "(!" <> pPrint ast <> ")"

data Link tag
    = LinkFinal (Final tag)
    | Link (MetaVar tag)

instance Pretty (Link tag) where
    pPrint (LinkFinal final) = "LinkFinal" <+> pPrint final
    pPrint (Link var) = "Link" <+> pPrint var

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
