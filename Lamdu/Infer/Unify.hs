-- | Type unification and meta-variables support
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
module Lamdu.Infer.Unify
    ( unifyTypeVar, unifyType, unifyComposite
    ) where

import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad (unless, zipWithM_)
import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Monoid as Monoid
import           Data.RefZone (Ref)
import           Data.Set (Set)
import qualified Data.Set as Set
import           Lamdu.Expr.Identifier (Tag(..))
import           Lamdu.Expr.Type (Type, Composite, AST(..), TParamId)
import qualified Lamdu.Expr.Type as Type
import           Lamdu.Expr.Type.Constraints (Constraints(..))
import           Lamdu.Expr.Type.Meta
import           Lamdu.Expr.Type.Tag (ASTTag(..), IsCompositeTag(..))
import qualified Lamdu.Infer.Monad as M
import           Pretty.Map ()
import           Text.PrettyPrint (Doc, (<+>))
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

import           Prelude.Compat hiding (tail)

----------------------
-- Unify composites --

type CompositeFields = Map Tag MetaType

-- TODO: Choose which to link into which weight/level-wise
writeLink :: Ref (Link tag) -> MetaVar tag -> M.Infer s ()
writeLink ref x = M.writeRef ref $ Link x

writeFinal :: Ref (Link tag) -> Final tag -> M.Infer s ()
writeFinal ref = M.writeRef ref . LinkFinal
--------------------
-- Unify type     --

unifyTInstParams ::
    M.Err -> Map TParamId MetaType -> Map TParamId MetaType -> M.Infer s ()
unifyTInstParams err uParams vParams
    | uSize /= vSize = M.throwError err
    | uSize == 0 = return ()
    | otherwise =
        zipWithM_ unifyParam (Map.toAscList uParams) (Map.toAscList vParams)
    where
        uSize = Map.size uParams
        vSize = Map.size vParams
        unifyParam (_, uParam) (_, vParam) = unifyType uParam vParam

unifyMatch :: Pretty v => Doc -> v -> Lens.Getting (Monoid.First a) v a -> M.Infer s a
unifyMatch expected vTyp prism =
    case vTyp ^? prism of
    Nothing -> M.throwError $ M.DoesNotUnify expected (pPrint vTyp)
    Just vcontent -> return vcontent

unifyTypeAST :: Type MetaTypeAST -> Type MetaTypeAST -> M.Infer s ()
unifyTypeAST uTyp@(TInst uName uParams) vTyp =
    case vTyp of
    TInst vName vParams | uName == vName ->
        {-# SCC "unifyTInstParams" #-}
        unifyTInstParams err uParams vParams
    _ -> M.throwError err
    where
        err = M.DoesNotUnify (pPrint uTyp) (pPrint vTyp)
unifyTypeAST (TRecord uRec) vTyp =
    do
        vRec <- unifyMatch "TRecord" vTyp Type._TRecord
        unifyComposite uRec vRec
unifyTypeAST (TSum uSum) vTyp =
    do
        vSum <- unifyMatch "TSum" vTyp Type._TSum
        unifyComposite uSum vSum
unifyTypeAST (TFun uArg uRes) vTyp =
    do
        (vArg, vRes) <- unifyMatch "TFun" vTyp Type._TFun
        unifyType uArg vArg
        unifyType uRes vRes
unifyTypeAST (TSkolem uName) vTyp =
    unifyMatch "TSkolem" vTyp (Type._TSkolem . Lens.only uName)

--------------------
-- Generic unify: --
--                --

-- | 'id' or 'flip'
type Order = forall a b. ((a -> a -> b) -> a -> a -> b)

data UnifyActions tag s = UnifyActions
    { actionUnifyASTs :: AST tag MetaTypeAST -> AST tag MetaTypeAST -> M.Infer s ()
    , actionUnifyUnboundToAST ::
          Order ->
          (MetaVar tag, Constraints tag) ->
          (Link tag, AST tag MetaTypeAST) ->
          M.Infer s ()
    , actionUnifyUnbounds ::
          (MetaVar tag, Constraints tag) ->
          (MetaVar tag, Constraints tag) ->
          M.Infer s ()
    }

data UnifyEnv tag s = UnifyEnv
    { envActions :: {-# UNPACK #-}!(UnifyActions tag s)
    , envInfer :: M.Env s
    }

type Unify tag s = M.InferEnv (UnifyEnv tag s) s

unifyASTs :: AST tag MetaTypeAST -> AST tag MetaTypeAST -> Unify tag s ()
unifyASTs u v =
    do
        UnifyActions{actionUnifyASTs} <- M.askEnv <&> envActions
        actionUnifyASTs u v & infer

unifyUnboundToAST ::
    Order -> (MetaVar tag, Constraints tag) -> (Link tag, AST tag MetaTypeAST) -> Unify tag s ()
unifyUnboundToAST order u v =
    do
        UnifyActions{actionUnifyUnboundToAST} <- M.askEnv <&> envActions
        actionUnifyUnboundToAST order u v & infer

unifyUnbounds ::
    (MetaVar tag, Constraints tag) -> (MetaVar tag, Constraints tag) -> Unify tag s ()
unifyUnbounds u v =
    do
        UnifyActions{actionUnifyUnbounds} <- M.askEnv <&> envActions
        actionUnifyUnbounds u v & infer

infer :: M.Infer s a -> Unify tag s a
infer = M.localEnv envInfer

runUnify ::
    Monoid (Constraints tag) => UnifyActions tag s -> Unify tag s a -> M.Infer s a
runUnify actions act = M.localEnv (UnifyEnv actions) act

unifyVarToAST :: Order -> MetaVar tag -> AST tag MetaTypeAST -> Unify tag s ()
unifyVarToAST order uVar vAst =
    infer (M.repr uVar) >>= \case
    (_, Bound uAst) -> order unifyASTs uAst vAst
    (uRef, Unbound uCs) ->
        unifyUnboundToAST order (uRef, uCs) (LinkFinal (Bound vAst), vAst)

unify :: MetaTypeAST tag -> MetaTypeAST tag -> Unify tag s ()
unify (MetaTypeAST u) (MetaTypeAST v) = unifyASTs u v
unify (MetaTypeVar u) (MetaTypeAST v) = unifyVarToAST id   u v
unify (MetaTypeAST u) (MetaTypeVar v) = unifyVarToAST flip v u
unify (MetaTypeVar u) (MetaTypeVar v) =
    do
        (uRef, ur) <- M.repr u & infer
        (vRef, vr) <- M.repr v & infer
        unless (uRef == vRef) $
            case (ur, vr) of
            (Unbound uCs, Unbound vCs) ->
                unifyUnbounds (uRef, uCs) (vRef, vCs)
            -- Make link to the other (final) ref, and not to the
            -- direct AST info so we know to avoid reunify work in
            -- future unify calls
            (Unbound uCs, Bound vAst) ->
                unifyUnboundToAST id (uRef, uCs) (Link vRef, vAst)
            (Bound uAst, Unbound vCs) ->
                unifyUnboundToAST flip (vRef, vCs) (Link uRef, uAst)
            (Bound uAst, Bound vAst) ->
                do
                    writeLink uRef vRef & infer
                    unifyASTs uAst vAst

--------------------

typeActions :: UnifyActions 'TypeT s
typeActions =
    UnifyActions
    { actionUnifyASTs = unifyTypeAST
    , actionUnifyUnboundToAST =
      \_order (uRef, TypeConstraints) (vLink, _vAst) -> M.writeRef uRef vLink
    , actionUnifyUnbounds =
      \(uRef, uCs) (vRef, vCs) ->
      do
          writeLink uRef vRef
          M.writeRef vRef $ LinkFinal $ Unbound (uCs `mappend` vCs)
    }

unifyTypeVar :: MetaVar 'TypeT -> AST 'TypeT MetaTypeAST -> M.Infer s ()
unifyTypeVar var ast = unifyVarToAST id var ast & runUnify typeActions

unifyType :: MetaType -> MetaType -> M.Infer s ()
unifyType u v = {-# SCC "unifyType" #-}unify u v & runUnify typeActions

--------------------

-- precondition: size uFields == size vFields
unifyFields :: CompositeFields -> CompositeFields -> M.Infer s ()
unifyFields !uFields !vFields =
    zipWithM_ unifyField (Map.toAscList uFields) (Map.toAscList vFields)
    where
        unifyField (uName, uType) (vName, vType)
            | uName == vName = unifyType uType vType
            | otherwise =
              M.throwError $
              M.DoesNotUnify
              ("Composite:" <+> pPrint (Map.keys uFields))
              ("Composite:" <+> pPrint (Map.keys vFields))

mismatchedFields :: [Tag] -> [Tag] -> M.InferEnv env s x
mismatchedFields u v =
    M.throwError $
    M.DoesNotUnify
    ("Composite:" <+> pPrint u)
    ("Composite:" <+> pPrint v)

-- We already know we are record vals, and will re-read them
-- via flatten, so no need for unify's read of these:
unifyCompositeAST ::
    IsCompositeTag c =>
    CompositeFields -> CompositeFields ->
    Composite c MetaTypeAST ->
    Composite c MetaTypeAST ->
    M.Infer s ()
unifyCompositeAST !uFields !vFields TEmptyComposite TEmptyComposite =
    unifyFields uFields vFields
unifyCompositeAST !uFields !vFields TEmptyComposite (TCompositeExtend vn _ _) =
    mismatchedFields (Map.keys uFields) (vn : Map.keys vFields)
unifyCompositeAST !uFields !vFields (TCompositeExtend un _ _) TEmptyComposite =
    mismatchedFields (un : Map.keys uFields) (Map.keys vFields)
unifyCompositeAST !uFields !vFields (TCompositeExtend un ut ur) (TCompositeExtend vn vt vr)
    | un == vn =
        do
            unifyType ut vt
            unifyCompositeH uFields vFields ur vr
    | otherwise =
      unifyCompositeH (Map.insert un ut uFields) (Map.insert vn vt vFields) ur vr
unifyCompositeAST _ _ (TSkolem u) v = M.DoesNotUnify (pPrint u) (pPrint v) & M.throwError
unifyCompositeAST _ _ u (TSkolem v) = M.DoesNotUnify (pPrint u) (pPrint v) & M.throwError

unifyComposite ::
    IsCompositeTag c => MetaComposite c -> MetaComposite c ->
    M.Infer s ()
unifyComposite = unifyCompositeH Map.empty Map.empty

enforceConstraints :: Set Tag -> Constraints ('CompositeT c) -> M.Infer s ()
enforceConstraints tags (CompositeConstraints disallowed) =
    unless (Set.null dups) $ M.throwError $ M.DuplicateFields $ Set.toList dups
    where
        dups = disallowed `Set.intersection` tags

unifyCompositeOpenToClosed ::
    IsCompositeTag c =>
    (MetaVar ('CompositeT c), Constraints ('CompositeT c), CompositeFields) ->
    ( CompositeFields
    , Maybe (Type.TVarName ('CompositeT c), Constraints ('CompositeT c))
    ) -> M.Infer s ()
unifyCompositeOpenToClosed u v =
    do
        unless (Map.null uniqueUFields) $ M.throwError $
            M.DoesNotUnify "[]" (pPrint (Map.keys uniqueUFields))
        closedTail <-
            case mSkolemConstraints of
            Just (skolemName, skolemConstraints) ->
                do
                    enforceConstraints (Map.keysSet uniqueUFields) skolemConstraints
                    Type.TSkolem skolemName & return
            Nothing -> return TEmptyComposite
        -- Validate no disallowed v-fields (in u constraints):
        enforceConstraints (Map.keysSet vFields) uCs
        let wrapField name typ = TCompositeExtend name typ . MetaTypeAST
        let uniqueVAST = Map.foldrWithKey wrapField closedTail uniqueVFields
        writeFinal uRef (Bound uniqueVAST)
    where
        (uRef, uCs, !uFields) = u
        (!vFields, mSkolemConstraints) = v
        uniqueUFields = uFields `Map.difference` vFields
        uniqueVFields = vFields `Map.difference` uFields

{-# INLINE unifyCompositeOpenToOpen #-}
unifyCompositeOpenToOpen ::
    IsCompositeTag c =>
    CompositeFields ->
    CompositeFields ->
    (MetaVar ('CompositeT c), Constraints ('CompositeT c)) ->
    (MetaVar ('CompositeT c), Constraints ('CompositeT c)) ->
    M.Infer s ()
unifyCompositeOpenToOpen !uFields !vFields (uRef, uCs) (vRef, vCs)
    | Map.null uFields && Map.null vFields =
      do
          writeLink uRef vRef
          writeFinal vRef $ Unbound (uCs `mappend` vCs)
    | otherwise =
      do
          commonRest <- M.freshRef cs
          let withWrap x = (MetaTypeAST x, LinkFinal (Bound x))
          let wrapField name typ =
                  withWrap . TCompositeExtend name typ . fst
          let wrapFields =
                  snd . Map.foldrWithKey wrapField
                  ( MetaTypeVar commonRest
                  , Link commonRest
                  )
          let writeCompositeTail ref = M.writeRef ref . wrapFields
          writeCompositeTail uRef uniqueVFields
          writeCompositeTail vRef uniqueUFields
    where
        cs = uCs `mappend` vCs
        uniqueUFields = uFields `Map.difference` vFields
        uniqueVFields = vFields `Map.difference` uFields

-- precondition: size uFields == size vFields
-- Unify of an open composite(u) with a partially-known composite(v) (which
-- may be open or closed)
unifyCompositeOpenToAST ::
    IsCompositeTag c =>
    CompositeFields ->
    CompositeFields ->
    (MetaVar ('CompositeT c), Constraints ('CompositeT c)) ->
    (Link ('CompositeT c), Type.Composite c MetaTypeAST) ->
    M.Infer s ()
unifyCompositeOpenToAST !uFields !vFields (uRef, uCs) (_vLink, vAST) =
    go vFields vAST
    where
        go !allVFields TEmptyComposite =
            unifyCompositeOpenToClosed (uRef, uCs, uFields) (allVFields, Nothing)
        go !allVFields (TSkolem skolemName) =
            do
                constraints <- M.lookupSkolem skolemName
                unifyCompositeOpenToClosed (uRef, uCs, uFields)
                    (allVFields, Just (skolemName, constraints))
        go !allVFields (TCompositeExtend n t r) =
            case r of
            MetaTypeAST rest -> go allVFields' rest
            MetaTypeVar restVar ->
                M.repr restVar >>= \case
                (_, Bound rest) -> go allVFields' rest
                (restRef, Unbound restCs) ->
                    -- v is Open:
                    unifyCompositeOpenToOpen uFields allVFields'
                    (uRef, uCs) (restRef, restCs)
            where
                allVFields' = Map.insert n t allVFields

unifyCompositeH ::
    IsCompositeTag c =>
    CompositeFields -> CompositeFields ->
    MetaComposite c -> MetaComposite c ->
    M.Infer s ()
unifyCompositeH !uFields !vFields u v =
    -- TODO: Assert Map.size uFields == Map.size vFields ?
    {-# SCC "unifyComposite" #-}
    unify u v
    & runUnify UnifyActions
    { actionUnifyASTs = unifyCompositeAST uFields vFields
    , actionUnifyUnboundToAST =
      \order -> order unifyCompositeOpenToAST uFields vFields
    , actionUnifyUnbounds = unifyCompositeOpenToOpen uFields vFields
    }
