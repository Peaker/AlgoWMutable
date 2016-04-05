-- | Inference Scope
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
module Lamdu.Infer.Scope
    ( Scope
    , newScope, emptyScope
    , insertLocal
    , lookupLocal, lookupGlobal, lookupSkolem
    ) where

import           Control.Lens.Operators
import qualified Control.Lens as Lens
import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Lamdu.Expr.Type as Type
import           Lamdu.Expr.Type.Constraints (Constraints)
import           Lamdu.Expr.Type.Scheme (Scheme, SchemeBinders(..))
import           Lamdu.Expr.Type.Tag
    ( ASTTag(..), IsTag(..), ASTTagEquality(..), CompositeTagEquality(..) )
import qualified Lamdu.Expr.Val as Val
import           Pretty.Map ()

import           Prelude.Compat

data Scope t = Scope
    { _scopeSkolems :: SchemeBinders
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
    case tagRefl :: ASTTagEquality tag  of
    IsTypeT -> tvBinders ^. Lens.at idx
    IsCompositeT IsRecordC -> rtvBinders ^. Lens.at idx
    IsCompositeT IsSumC -> stvBinders ^. Lens.at idx
    where
        SchemeBinders tvBinders rtvBinders stvBinders = _scopeSkolems

{-# INLINE insertLocal #-}
insertLocal :: Val.Var -> t -> Scope t -> Scope t
insertLocal name typ (Scope skolems locals globals) =
    Scope skolems (Map.insert name typ locals) globals
