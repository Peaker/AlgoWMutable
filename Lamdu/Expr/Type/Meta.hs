{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
-- | Types with meta-variables

module Lamdu.Expr.Type.Meta
    ( Final(..), _Unbound, _Bound
    , Link(..), _LinkFinal, _Link
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

data Final tag
    = Unbound (Constraints tag)
    | Bound (Type.AST tag MetaTypeAST)

data Link tag
    = LinkFinal (Final tag)
    | Link (MetaVar tag)

-- TODO: Remove this newtype?
newtype MetaVar tag = MetaVar { metaVarRef :: RefZone.Ref (Link tag) }

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

Lens.makePrisms ''Link
Lens.makePrisms ''Final
Lens.makeLenses ''MetaVar

type MetaType = MetaTypeAST 'TypeT
type MetaComposite c = MetaTypeAST ('CompositeT c)
