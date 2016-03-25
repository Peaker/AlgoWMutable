-- | Inference Scope
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE DataKinds #-}
module Type.Infer.Scope
    ( Scope
    , newScope, emptyScope
    , insertLocal
    , lookupLocal, lookupGlobal
    ) where

import           Data.Map (Map)
import qualified Data.Map as Map
import           Pretty.Map ()
import           Type.Tag (ASTTag(..))
import           Type.Scheme (Scheme)
import qualified Val

import           Prelude.Compat

data Scope t = Scope
    { _scopeLocals :: Map Val.Var t
    , _scopeGlobals :: Map Val.GlobalId (Scheme 'TypeT)
    }

lookupLocal :: Val.Var -> Scope t -> Maybe t
lookupLocal v scope =
    Map.lookup v (_scopeLocals scope)

lookupGlobal :: Val.GlobalId -> Scope t -> Maybe (Scheme 'TypeT)
lookupGlobal v scope =
    Map.lookup v (_scopeGlobals scope)

newScope :: Map Val.GlobalId (Scheme 'TypeT) -> Scope t
newScope = Scope Map.empty

emptyScope :: Scope t
emptyScope = Scope Map.empty Map.empty

{-# INLINE insertLocal #-}
insertLocal :: Val.Var -> t -> Scope t -> Scope t
insertLocal name typ (Scope locals globals) =
    Scope (Map.insert name typ locals) globals
