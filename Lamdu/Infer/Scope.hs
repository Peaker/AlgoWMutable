-- | Inference Scope
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE DataKinds #-}
module Lamdu.Infer.Scope
    ( Scope
    , newScope, emptyScope
    , insertLocal
    , lookupLocal, lookupGlobal
    ) where

import           Data.Map (Map)
import qualified Data.Map as Map
import           Lamdu.Expr.Type.Scheme (Scheme)
import           Lamdu.Expr.Type.Tag (ASTTag(..))
import qualified Lamdu.Expr.Val as Val
import           Pretty.Map ()

import           Prelude.Compat

data Scope t = Scope
    { _scopeLocals :: Map Val.Var t
    , _scopeGlobals :: Map Val.Var (Scheme 'TypeT)
    }

lookupLocal :: Val.Var -> Scope t -> Maybe t
lookupLocal v scope =
    Map.lookup v (_scopeLocals scope)

lookupGlobal :: Val.Var -> Scope t -> Maybe (Scheme 'TypeT)
lookupGlobal v scope =
    Map.lookup v (_scopeGlobals scope)

newScope :: Map Val.Var (Scheme 'TypeT) -> Scope t
newScope = Scope Map.empty

emptyScope :: Scope t
emptyScope = Scope Map.empty Map.empty

{-# INLINE insertLocal #-}
insertLocal :: Val.Var -> t -> Scope t -> Scope t
insertLocal name typ (Scope locals globals) =
    Scope (Map.insert name typ locals) globals
