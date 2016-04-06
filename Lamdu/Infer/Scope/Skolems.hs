-- | Hierarchial skolems' scope
{-# LANGUAGE NoImplicitPrelude #-}
module Lamdu.Infer.Scope.Skolems
    ( SkolemScopeId(..)
    , SkolemScope(..), new
    ) where

import Control.Lens.Operators
import Data.Maybe (fromMaybe)
import Lamdu.Expr.Type.Scheme (SchemeBinders)
import Text.PrettyPrint (text, (<>))
import Text.PrettyPrint.HughesPJClass (Pretty(..))

import Prelude.Compat

newtype SkolemScopeId = SkolemScopeId Int
   deriving (Eq, Ord, Show)
instance Pretty SkolemScopeId where
    pPrint (SkolemScopeId i) = text "SkolemScope:" <> pPrint i

data SkolemScope = SkolemScope
   { skolemScopeLevel :: !Int -- for fast MRA finding
   , skolemScopeId :: !SkolemScopeId -- this is unique so allows fast scope comparison
   , skolemScopeParent :: !(Maybe SkolemScope)
   , -- lazily-built binders that mconcat the parents' chain
     skolemScopeBinders :: SchemeBinders
   }
instance Pretty SkolemScope where
    pPrint (SkolemScope _level scopeId _scopeParent _binders) =
        text "SkolemScope:" <> pPrint scopeId

new ::
    SkolemScope -> -- parent
    SkolemScopeId -> -- the scope id must be unique!
    SchemeBinders ->
    SkolemScope
new parent uniqueId binders =
    SkolemScope
    (1 + skolemScopeLevel parent) uniqueId (Just parent)
    (mappend binders (skolemScopeBinders parent))

-- precondition: the levels are equal
intersectSameLevel :: SkolemScope -> SkolemScope -> SkolemScope
intersectSameLevel s0@(SkolemScope level0 id0 parent0 _) (SkolemScope level1 id1 parent1 _)
    | id0 == id1 = s0
    | otherwise =
      intersectSameLevel <$> parent0 <*> parent1
      -- If both levels are the same, then they must have parents and eventually meet
      & fromMaybe (error msg)
    where
        msg =
            unwords
            [ "SkolemScope level invariants broken:", show id0, "at", show level0
            , "(vs", show id1, "at", show level1, ")"
            ]

walkup :: Int -> SkolemScope -> SkolemScope
walkup destLevel =
    go
    where
        go scope
            | skolemScopeLevel scope == destLevel = scope
            | otherwise =
              maybe (error "SkolemScope level invariants broken")
              go (skolemScopeParent scope)

instance Monoid SkolemScope where
    mempty = -- the root:
        SkolemScope 0 (SkolemScopeId 0) Nothing mempty
    mappend
        s0@(SkolemScope level0 id0 _ _)
        s1@(SkolemScope level1 id1 _ _)
        | id0 == id1 = s0
        | level0 >= level1 = intersectSameLevel (walkup level1 s0) s1
        | otherwise = intersectSameLevel s0 (walkup level0 s1)
