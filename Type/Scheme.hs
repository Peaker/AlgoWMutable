{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
module Type.Scheme
    ( SchemeBinders(..)
    , Scheme(..), forAll
    ) where

import           Control.DeepSeq (NFData(..))
import           Control.Lens.Operators
import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Pretty.Map ()
import           Pretty.Utils ((<+?>), intercalate)
import           Text.PrettyPrint (Doc, (<>))
import           Text.PrettyPrint.HughesPJClass (Pretty(..))
import qualified Type
import           Type.Constraints (Constraints(..))
import           Type.Pure (T(..), TVarName(..))
import           Type.Tag (ASTTag(..), RecordT, SumT)

import           Prelude.Compat

type TVarBinders tag = Map (TVarName tag) (Constraints tag)

data SchemeBinders = SchemeBinders
    { schemeTypeBinders :: TVarBinders 'TypeT
    , schemeRecordBinders :: TVarBinders RecordT
    , schemeSumBinders :: TVarBinders SumT
    }
instance NFData SchemeBinders where
    rnf (SchemeBinders x y z) = rnf x `seq` rnf y `seq` rnf z
instance Monoid SchemeBinders where
    mempty = SchemeBinders Map.empty Map.empty Map.empty
    mappend (SchemeBinders t0 r0 s0) (SchemeBinders t1 r1 s1)
        | enableAssertions =
            SchemeBinders
            -- TODO: Can use assert-same-constraints and compile out for
            -- perf instead of mappend
            (Map.unionWith assertSameConstraints t0 t1)
            (Map.unionWith assertSameConstraints r0 r1)
            (Map.unionWith assertSameConstraints s0 s1)
        | otherwise =
            SchemeBinders
            (Map.union t0 t1)
            (Map.union r0 r1)
            (Map.union s0 s1)
        where
            enableAssertions = False
            assertSameConstraints x y
                | x == y = x
                | otherwise =
                  "Differing constraints of same " ++
                  "unification variable encountered"
                  & error

nullBinders :: SchemeBinders -> Bool
nullBinders (SchemeBinders a b c) = Map.null a && Map.null b && Map.null c

data Scheme tag = Scheme
    { schemeBinders :: SchemeBinders
    , schemeType :: T tag
    }
instance NFData (Scheme tag) where
    rnf (Scheme x y) = rnf x `seq` rnf y

pPrintTV :: (TVarName tag, Constraints tag) -> Doc
pPrintTV (tv, constraints) =
    "∀a" <> pPrint tv <> suffix constraints
    where
        suffix :: Constraints tag -> Doc
        suffix TypeConstraints = ""
        suffix (CompositeConstraints cs) =
            "∉" <> (intercalate " " . map pPrint) (Set.toList cs)

instance Pretty SchemeBinders where
    pPrint (SchemeBinders tvs rtvs stvs) =
        intercalate " " $
        map pPrintTV (Map.toList tvs) ++
        map pPrintTV (Map.toList rtvs) ++
        map pPrintTV (Map.toList stvs)

instance Pretty (Type.AST tag T) => Pretty (Scheme tag) where
    pPrint (Scheme binders typ)
        | nullBinders binders = pPrint typ
        | otherwise = pPrint binders <> "." <+?> pPrint typ

forAll ::
    Int -> Int -> Int ->
    ([T 'TypeT] -> [T RecordT] -> [T SumT] -> T tag) ->
    Scheme tag
forAll nTvs nRtvs nStvs mkType =
    Scheme (SchemeBinders cTvs cRtvs cStvs) $
    mkType (map TVar tvs) (map TVar rtvs) (map TVar stvs)
    where
        cTvs = Map.fromList [ (tv, mempty) | tv <- tvs ]
        cRtvs = Map.fromList [ (tv, mempty) | tv <- rtvs ]
        cStvs = Map.fromList [ (tv, mempty) | tv <- stvs ]
        tvs = map TVarName [1..nTvs]
        rtvs = map TVarName [nTvs+1..nTvs+nRtvs]
        stvs = map TVarName [nTvs+nRtvs+1..nTvs+nRtvs+nStvs]
