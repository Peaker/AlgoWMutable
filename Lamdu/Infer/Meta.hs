{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
-- | Types with meta-variables

module Lamdu.Infer.Meta
    ( Final(..), _Unbound, _Bound
    , Link(..), _LinkFinal, _Link
    , MetaVar, MetaTypeAST(..), MetaType, MetaComposite
    ) where

import           Control.DeepSeq (NFData(..))
import qualified Control.Lens as Lens
import qualified Data.RefZone as RefZone
import qualified Lamdu.Expr.Type as Type
import           Lamdu.Expr.Type.Constraints (Constraints)
import           Lamdu.Expr.Type.Tag (ASTTag(..))
import           Text.PrettyPrint ((<>), (<+>))
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

data Final tag
    = Unbound (Constraints tag)
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
    = MetaTypeVar (MetaVar tag)
    | MetaTypeAST (Type.AST tag MetaTypeAST)
instance NFData (MetaTypeAST tag) where
    rnf (MetaTypeVar x) = rnf x
    rnf (MetaTypeAST x) = rnf x
instance Pretty (Type.AST tag MetaTypeAST) => Pretty (MetaTypeAST tag) where
    pPrint (MetaTypeVar pos) = pPrint pos
    pPrint (MetaTypeAST t) = pPrint t

Lens.makePrisms ''Link
Lens.makePrisms ''Final

type MetaType = MetaTypeAST 'TypeT
type MetaComposite c = MetaTypeAST ('CompositeT c)
