-- | Inference Scope
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DataKinds #-}
module Lamdu.Infer.Scope
    ( Scope
    , skolemScope
    , newScope, emptyScope
    , insertLocal
    , lookupLocal, lookupGlobal, lookupNominal
    , extendSkolemScope
    ) where

import           Control.DeepSeq (NFData(..))
import           Data.Map (Map)
import qualified Data.Map.Strict as Map
import           Lamdu.Expr.Identifier (NominalId)
import           Lamdu.Expr.Type.Nominal (Nominal)
import           Lamdu.Expr.Type.Scheme (Scheme, SchemeBinders)
import           Lamdu.Expr.Type.Tag (ASTTag(..))
import qualified Lamdu.Expr.Val as Val
import           Lamdu.Infer.Meta (MetaType)
import           Lamdu.Infer.Scope.Skolems (SkolemScope(..), SkolemScopeId)
import qualified Lamdu.Infer.Scope.Skolems as Skolems
import           Pretty.Map ()

import           Prelude.Compat

data Scope = Scope
    { _scopeSkolems :: !SkolemScope
    , _scopeLocals :: !(Map Val.Var MetaType)
    , _scopeNominals :: !(Map NominalId Nominal)
    , _scopeGlobals :: !(Map Val.Var (Scheme 'TypeT))
    }
instance NFData Scope where
    rnf (Scope a b c d) = rnf a `seq` rnf b `seq` rnf c `seq` rnf d

newScope :: Map NominalId Nominal -> Map Val.Var (Scheme 'TypeT) -> Scope
newScope = Scope mempty mempty

emptyScope :: Scope
emptyScope = Scope mempty mempty mempty mempty

lookupLocal :: Val.Var -> Scope -> Maybe MetaType
lookupLocal v Scope{_scopeLocals} =
    Map.lookup v _scopeLocals

lookupGlobal :: Val.Var -> Scope -> Maybe (Scheme 'TypeT)
lookupGlobal v Scope{_scopeGlobals} = Map.lookup v _scopeGlobals

lookupNominal :: NominalId -> Scope -> Maybe Nominal
lookupNominal v Scope{_scopeNominals} = Map.lookup v _scopeNominals

{-# INLINE insertLocal #-}
insertLocal :: Val.Var -> MetaType -> Scope -> Scope
insertLocal name typ (Scope skolems locals nominals globals) =
    Scope skolems (Map.insert name typ locals) nominals globals

skolemScope :: Scope -> SkolemScope
skolemScope = _scopeSkolems

extendSkolemScope :: SkolemScopeId -> SchemeBinders -> Scope -> Scope
extendSkolemScope freshId binders scope =
    scope{_scopeSkolems = Skolems.new (_scopeSkolems scope) freshId binders}
