{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
module Lamdu.Expr.Type.Scheme
    ( TVarBinders
    , SchemeBinders(..)
    , schemeBindersSingleton, schemeBindersLookup
    , Scheme(..), forAll
    ) where

import           Control.DeepSeq (NFData(..))
import           Control.Lens.Operators
import           Control.Lens.Tuple
import           Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import           Data.Semigroup (Semigroup)
import qualified Data.Semigroup as Semigroup
import qualified Data.Set as Set
import qualified Lamdu.Expr.Type as Type
import           Lamdu.Expr.Type.Constraints (Constraints(..))
import           Lamdu.Expr.Type.Pure (T(..))
import           Lamdu.Expr.Type.Tag
    ( IsTag(..), RecordT, SumT, ASTTag(..), ASTTagEquality(..)
    , CompositeTagEquality(..) )
import           Pretty.Map ()
import           Pretty.Utils ((<+?>), intercalate)
import           Text.PrettyPrint (Doc, (<>))
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

import           Prelude.Compat

type TVarBinders tag = IntMap (Constraints tag)

tvarBindersToList :: TVarBinders tag -> [(Type.TVarName tag, Constraints tag)]
tvarBindersToList = map (_1 %~ Type.TVarName) . IntMap.toList

tvarBindersFromList :: [(Type.TVarName tag, Constraints tag)] -> TVarBinders tag
tvarBindersFromList = IntMap.fromList . map (_1 %~ Type._tVarName)

data SchemeBinders = SchemeBinders
    { schemeTypeBinders :: TVarBinders 'TypeT
    , schemeRecordBinders :: TVarBinders RecordT
    , schemeSumBinders :: TVarBinders SumT
    }
instance NFData SchemeBinders where
    rnf (SchemeBinders x y z) = rnf x `seq` rnf y `seq` rnf z
instance Semigroup SchemeBinders where
    SchemeBinders t0 r0 s0 <> SchemeBinders t1 r1 s1 =
        SchemeBinders
        (IntMap.unionWith assertSameConstraints t0 t1)
        (IntMap.unionWith assertSameConstraints r0 r1)
        (IntMap.unionWith assertSameConstraints s0 s1)
        where
            assertSameConstraints x y
                | x == y = x
                | otherwise =
                  "Differing constraints of same " ++
                  "unification variable encountered"
                  & error
instance Monoid SchemeBinders where
    mempty = SchemeBinders IntMap.empty IntMap.empty IntMap.empty
    mappend = (Semigroup.<>)

nullBinders :: SchemeBinders -> Bool
nullBinders (SchemeBinders a b c) = IntMap.null a && IntMap.null b && IntMap.null c

data Scheme tag = Scheme
    { schemeBinders :: SchemeBinders
    , schemeType :: T tag
    }
instance NFData (Scheme tag) where
    rnf (Scheme x y) = rnf x `seq` rnf y

pPrintTV :: (Type.TVarName tag, Constraints tag) -> Doc
pPrintTV (tv, constraints) =
    "∀" <> pPrint tv <> suffix constraints
    where
        suffix :: Constraints tag -> Doc
        suffix TypeConstraints = ""
        suffix (CompositeConstraints cs) =
            "∉" <> (intercalate " " . map pPrint) (Set.toList cs)

instance Pretty SchemeBinders where
    pPrint (SchemeBinders tvs rtvs stvs) =
        intercalate " " $
        map pPrintTV (tvarBindersToList tvs) ++
        map pPrintTV (tvarBindersToList rtvs) ++
        map pPrintTV (tvarBindersToList stvs)

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
    mkType
    (map mkTv tvNames)
    (map mkTv rtvNames)
    (map mkTv stvNames)
    where
        mkTv = T . Type.TSkolem
        cTvs = tvarBindersFromList [ (tv, mempty) | tv <- tvNames ]
        cRtvs = tvarBindersFromList [ (tv, mempty) | tv <- rtvNames ]
        cStvs = tvarBindersFromList [ (tv, mempty) | tv <- stvNames ]
        tvNames = map Type.TVarName [1..nTvs]
        rtvNames = map Type.TVarName [nTvs+1..nTvs+nRtvs]
        stvNames = map Type.TVarName [nTvs+nRtvs+1..nTvs+nRtvs+nStvs]

schemeBindersSingleton ::
    forall tag. IsTag tag => Type.TVarName tag -> Constraints tag -> SchemeBinders
schemeBindersSingleton (Type.TVarName tvName) cs =
    case tagRefl :: ASTTagEquality tag of
    IsTypeT -> mempty { schemeTypeBinders = binders }
    IsCompositeT IsRecordC -> mempty { schemeRecordBinders = binders }
    IsCompositeT IsSumC -> mempty { schemeSumBinders = binders }
    where
        binders = IntMap.singleton tvName cs

schemeBindersLookup ::
    forall tag. IsTag tag =>
    Type.TVarName tag -> SchemeBinders -> Maybe (Constraints tag)
schemeBindersLookup (Type.TVarName idx) =
    case tagRefl :: ASTTagEquality tag  of
    IsTypeT                -> IntMap.lookup idx . schemeTypeBinders
    IsCompositeT IsRecordC -> IntMap.lookup idx . schemeRecordBinders
    IsCompositeT IsSumC    -> IntMap.lookup idx . schemeSumBinders
