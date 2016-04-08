-- | Inference Scope
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
module Lamdu.Infer.Scope
    ( Scope
    , skolemScope
    , newScope, emptyScope
    , insertLocal
    , lookupLocal, lookupGlobal, lookupSkolem, lookupNominal
    , extendSkolemScope
    ) where

import           Control.Lens.Operators
import           Data.Map (Map)
import qualified Data.Map as Map
import           Lamdu.Expr.Identifier (NominalId)
import qualified Lamdu.Expr.Type as Type
import           Lamdu.Expr.Type.Constraints (Constraints)
import           Lamdu.Expr.Type.Nominal (Nominal)
import           Lamdu.Expr.Type.Scheme (Scheme, SchemeBinders, schemeBindersLookup)
import           Lamdu.Expr.Type.Tag (ASTTag(..), IsTag(..))
import qualified Lamdu.Expr.Val as Val
import           Lamdu.Infer.Scope.Skolems (SkolemScope(..), SkolemScopeId)
import qualified Lamdu.Infer.Scope.Skolems as Skolems
import           Pretty.Map ()

import           Prelude.Compat

data Scope t = Scope
    { _scopeSkolems :: SkolemScope
    , _scopeLocals :: Map Val.Var t
    , _scopeNominals :: Map NominalId Nominal
    , _scopeGlobals :: Map Val.Var (Scheme 'TypeT)
    }

newScope :: Map NominalId Nominal -> Map Val.Var (Scheme 'TypeT) -> Scope t
newScope = Scope mempty mempty

emptyScope :: Scope t
emptyScope = Scope mempty mempty mempty mempty

lookupLocal :: Val.Var -> Scope t -> Maybe t
lookupLocal v Scope{_scopeLocals} =
    Map.lookup v _scopeLocals

lookupGlobal :: Val.Var -> Scope t -> Maybe (Scheme 'TypeT)
lookupGlobal v Scope{_scopeGlobals} = Map.lookup v _scopeGlobals

lookupNominal :: NominalId -> Scope t -> Maybe Nominal
lookupNominal v Scope{_scopeNominals} = Map.lookup v _scopeNominals

lookupSkolem ::
    forall tag t. IsTag tag =>
    Type.TVarName tag -> Scope t -> Maybe (Constraints tag)
lookupSkolem tVarName Scope{_scopeSkolems} =
    skolemScopeBinders _scopeSkolems
    & schemeBindersLookup tVarName

{-# INLINE insertLocal #-}
insertLocal :: Val.Var -> t -> Scope t -> Scope t
insertLocal name typ (Scope skolems locals nominals globals) =
    Scope skolems (Map.insert name typ locals) nominals globals

skolemScope :: Scope t -> SkolemScope
skolemScope = _scopeSkolems

extendSkolemScope :: SkolemScopeId -> SchemeBinders -> Scope t -> Scope t
extendSkolemScope freshId binders scope =
    scope{_scopeSkolems = Skolems.new (_scopeSkolems scope) freshId binders}
