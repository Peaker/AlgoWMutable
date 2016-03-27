{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
-- | Types with meta-variables

module Lamdu.Expr.Type.Meta
    ( IsBound(..), _Unbound, _Bound
    , MetaVar(..), MetaTypeAST(..), MetaType, MetaComposite
    ) where

import           Control.DeepSeq (NFData(..))
import qualified Control.Lens as Lens
import           Data.Monoid ((<>))
import qualified Data.RefZone as RefZone
import qualified Lamdu.Expr.Type as Type
import           Lamdu.Expr.Type.Constraints (Constraints)
import           Lamdu.Expr.Type.Tag (ASTTag(..))
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

data IsBound tag bound
    = Unbound (Constraints tag)
    | Bound bound
Lens.makePrisms ''IsBound

newtype MetaVar tag = MetaVar { metaVarRef :: RefZone.Ref (IsBound tag (MetaTypeAST tag)) }

instance NFData (MetaVar tag) where rnf (MetaVar r) = rnf r
instance Pretty (MetaVar tag) where pPrint (MetaVar r) = "?" <> pPrint r

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
