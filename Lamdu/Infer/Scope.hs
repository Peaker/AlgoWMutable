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
    , lookupLocal, lookupGlobal, lookupSkolem
    ) where

import           Control.Lens.Operators
import qualified Data.IntMap as IntMap
import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Lamdu.Expr.Type as Type
import           Lamdu.Expr.Type.Constraints (Constraints)
import           Lamdu.Expr.Type.Scheme (Scheme, SchemeBinders(..))
import           Lamdu.Expr.Type.Tag
    ( ASTTag(..), IsTag(..), ASTTagEquality(..), CompositeTagEquality(..) )
import qualified Lamdu.Expr.Val as Val
import           Lamdu.Infer.Scope.Skolems (SkolemScope(..))
import           Pretty.Map ()

import           Prelude.Compat

data Scope t = Scope
    { _scopeSkolems :: SkolemScope
    , _scopeLocals :: Map Val.Var t
    , _scopeGlobals :: Map Val.Var (Scheme 'TypeT)
    }

newScope :: Map Val.Var (Scheme 'TypeT) -> Scope t
newScope = Scope mempty Map.empty

emptyScope :: Scope t
emptyScope = Scope mempty Map.empty Map.empty

lookupLocal :: Val.Var -> Scope t -> Maybe t
lookupLocal v Scope{_scopeLocals} =
    Map.lookup v _scopeLocals

lookupGlobal :: Val.Var -> Scope t -> Maybe (Scheme 'TypeT)
lookupGlobal v Scope{_scopeGlobals} = Map.lookup v _scopeGlobals

lookupSkolem ::
    forall tag t. IsTag tag =>
    Type.TVarName tag -> Scope t -> Maybe (Constraints tag)
lookupSkolem (Type.TVarName idx) Scope{_scopeSkolems} =
    skolemScopeBinders _scopeSkolems
    & case tagRefl :: ASTTagEquality tag  of
      IsTypeT                -> IntMap.lookup idx . schemeTypeBinders
      IsCompositeT IsRecordC -> IntMap.lookup idx . schemeRecordBinders
      IsCompositeT IsSumC    -> IntMap.lookup idx . schemeSumBinders

{-# INLINE insertLocal #-}
insertLocal :: Val.Var -> t -> Scope t -> Scope t
insertLocal name typ (Scope skolems locals globals) =
    Scope skolems (Map.insert name typ locals) globals

skolemScope :: Scope t -> SkolemScope
skolemScope = _scopeSkolems
