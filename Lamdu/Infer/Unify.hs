{-# LANGUAGE NamedFieldPuns #-}
-- | Type unification and meta-variables support
{-# LANGUAGE NoImplicitPrelude #-}
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
import           Data.Foldable (sequenceA_)
import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Monoid as Monoid
import qualified Data.Set as Set
import           Lamdu.Expr.Identifier (Tag(..))
import           Lamdu.Expr.Type (Type, Composite, AST(..), TParamId)
import qualified Lamdu.Expr.Type as Type
import           Lamdu.Expr.Type.Constraints (Constraints(..))
import           Lamdu.Expr.Type.Meta
import           Lamdu.Expr.Type.Tag (ASTTag(..), IsCompositeTag(..))
import qualified Lamdu.Infer.Monad as M
import           Pretty.Map ()
import           Pretty.Utils (intercalate)
import           Text.PrettyPrint (Doc, (<+>))
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

import           Prelude.Compat hiding (tail)

----------------------
-- Unify composites --

data CompositeTail c
    = CompositeTailClosed
    | CompositeTailOpen (MetaVar ('CompositeT c)) (Constraints ('CompositeT c))
    -- TODO(Review): The "Constraints" cache above is necessary? Can it become stale?

type CompositeFields = Map Tag MetaType

data FlatComposite c = FlatComposite
    { _fcFields :: CompositeFields
    , __fcTailUF :: CompositeTail c
    }

Lens.makeLenses ''FlatComposite

flattenVal :: Composite c MetaTypeAST -> M.Infer s (FlatComposite c)
flattenVal TEmptyComposite =
    return $ FlatComposite Map.empty CompositeTailClosed
flattenVal (TCompositeExtend n t r) =
    flatten r <&> fcFields . Lens.at n ?~ t

flatten :: MetaComposite c -> M.Infer s (FlatComposite c)
flatten (MetaTypeAST ast) = flattenVal ast
flatten (MetaTypeVar ref) =
    M.repr ref >>= \case
    (finalRef, Unbound cs) ->
        return $ FlatComposite Map.empty $ CompositeTailOpen finalRef cs
    (_, Bound ast) -> flattenVal ast

unflatten :: IsCompositeTag c => FlatComposite c -> MetaComposite c
unflatten (FlatComposite fields tail) =
    {-# SCC "unflatten" #-}Map.toList fields & go
    where
        go [] = case tail of
            CompositeTailClosed -> MetaTypeAST TEmptyComposite
            CompositeTailOpen ref _ -> MetaTypeVar ref
        go ((name, typ):fs) =
            go fs & TCompositeExtend name typ & MetaTypeAST

prettyFieldNames :: Map Tag a -> Doc
prettyFieldNames = intercalate " " . map pPrint . Map.keys

ascKeys :: Map a b -> [a]
ascKeys = map fst . Map.toAscList

{-# INLINE unifyCompositesClosedClosed #-}
unifyCompositesClosedClosed :: CompositeFields -> CompositeFields -> M.Infer s ()
unifyCompositesClosedClosed uFields vFields
    | ascKeys uFields == ascKeys vFields = return ()
    | otherwise =
          M.throwError $
          M.DoesNotUnify
          ("Record fields:" <+> prettyFieldNames uFields)
          ("Record fields:" <+> prettyFieldNames vFields)

flatConstraintsPropagate :: Constraints ('CompositeT c) -> FlatComposite c -> M.Infer s ()
flatConstraintsPropagate outerConstraints@(CompositeConstraints outerDisallowed) flatComposite =
    do
        unless (Set.null duplicates) $ M.throwError $ M.DuplicateFields $
            Set.toList duplicates
        case innerTail of
            CompositeTailClosed -> return ()
            CompositeTailOpen ref innerConstraints ->
                M.writeRef ref $ LinkFinal $ Unbound $ outerConstraints `mappend` innerConstraints
    where
        duplicates = Set.intersection (Map.keysSet innerFields) outerDisallowed
        FlatComposite innerFields innerTail = flatComposite

constraintsPropagate :: Constraints tag -> AST tag MetaTypeAST -> M.Infer s ()
constraintsPropagate TypeConstraints _ = return ()
constraintsPropagate cs@CompositeConstraints{} inner =
    ({-# SCC "constraintsPropagate.flatten" #-}flattenVal inner) >>= flatConstraintsPropagate cs

writeCompositeTail ::
    IsCompositeTag c =>
    (MetaVar ('CompositeT c), Constraints ('CompositeT c)) ->
    FlatComposite c -> M.Infer s ()
writeCompositeTail (ref, cs) composite =
    do
        {-# SCC "flatConstraintsPropagate" #-}flatConstraintsPropagate cs composite
        M.writeRef ref $ case unflatten composite of
            MetaTypeAST ast -> LinkFinal $ Bound ast
            MetaTypeVar var -> Link var

{-# INLINE unifyCompositesOpenClosed #-}
unifyCompositesOpenClosed ::
    IsCompositeTag c =>
    (MetaVar ('CompositeT c), Constraints ('CompositeT c), CompositeFields) ->
    CompositeFields -> M.Infer s ()
unifyCompositesOpenClosed (openTailRef, CompositeConstraints openDisallowed, openFields) closedFields
    | not (Map.null uniqueOpenFields) =
          M.throwError $
          M.DoesNotUnify
          ("Record with at least fields:" <+> prettyFieldNames openFields)
          ("Record fields:" <+> prettyFieldNames closedFields)
    | not (Set.null disallowedFields) =
          M.throwError $ M.DuplicateFields $ Set.toList disallowedFields
    | otherwise =
          Map.foldrWithKey extend empty closedFields
          & LinkFinal . Bound
          & M.writeRef openTailRef
    where
        extend name typ = TCompositeExtend name typ . MetaTypeAST
        empty = TEmptyComposite
        disallowedFields = openDisallowed `Set.intersection` Map.keysSet uniqueClosedFields
        uniqueOpenFields = openFields `Map.difference` closedFields
        uniqueClosedFields = closedFields `Map.difference` openFields

{-# INLINE unifyCompositesOpenOpen #-}
unifyCompositesOpenOpen ::
    IsCompositeTag c =>
    (MetaVar ('CompositeT c), Constraints ('CompositeT c), CompositeFields) ->
    (MetaVar ('CompositeT c), Constraints ('CompositeT c), CompositeFields) ->
    M.Infer s ()
unifyCompositesOpenOpen (uRef, uCs, uFields) (vRef, vCs, vFields) =
    do
        commonRest <- M.freshRef cs <&> (`CompositeTailOpen` cs)
        writeCompositeTail (uRef, uCs) $ FlatComposite uniqueVFields commonRest
        writeCompositeTail (vRef, vCs) $ FlatComposite uniqueUFields commonRest
    where
        cs = uCs `mappend` vCs
        uniqueUFields = uFields `Map.difference` vFields
        uniqueVFields = vFields `Map.difference` uFields

-- We already know we are record vals, and will re-read them
-- via flatten, so no need for unify's read of these:
unifyCompositeAST ::
    IsCompositeTag c =>
    Composite c MetaTypeAST ->
    Composite c MetaTypeAST ->
    M.Infer s ()
unifyCompositeAST TEmptyComposite TEmptyComposite = return ()
unifyCompositeAST (TCompositeExtend un ut ur) (TCompositeExtend vn vt vr)
    | un == vn =
        do
            unifyType ut vt
            unifyComposite ur vr
unifyCompositeAST u v =
    do
        FlatComposite uFields uTail <- {-# SCC "unifyCompositeAST.flatten(u)" #-}flattenVal u
        FlatComposite vFields vTail <- {-# SCC "unifyCompositeAST.flatten(v)" #-}flattenVal v
        case (uTail, vTail) of
            (CompositeTailClosed, CompositeTailClosed) ->
                {-# SCC "unifyCompositesClosedClosed" #-}
                unifyCompositesClosedClosed uFields vFields
            (CompositeTailOpen uRef uCs, CompositeTailClosed) ->
                {-# SCC "unifyCompositesOpenClosed" #-}
                unifyCompositesOpenClosed (uRef, uCs, uFields) vFields
            (CompositeTailClosed, CompositeTailOpen vRef vCs) ->
                {-# SCC "unifyCompositesOpenClosed" #-}
                unifyCompositesOpenClosed (vRef, vCs, vFields) uFields
            (CompositeTailOpen uRef uCs, CompositeTailOpen vRef vCs) ->
                {-# SCC "unifyCompositesOpenOpen" #-}
                unifyCompositesOpenOpen (uRef, uCs, uFields) (vRef, vCs, vFields)
        -- We intersect-unify AFTER unifying the composite shapes, so
        -- we know the flat composites are accurate
        Map.intersectionWith unifyType uFields vFields
            & sequenceA_

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

--------------------
-- Generic unify: --
--                --

data UnifyActions tag s = UnifyActions
    { actionUnifyASTs :: AST tag MetaTypeAST -> AST tag MetaTypeAST -> M.Infer s ()
    , actionUnifyUnboundToAST :: Constraints tag -> AST tag MetaTypeAST -> M.Infer s ()
    , actionUnifyUnbounds :: Constraints tag -> Constraints tag -> M.Infer s (Constraints tag)
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

unifyUnboundToAST :: Constraints tag -> AST tag MetaTypeAST -> Unify tag s ()
unifyUnboundToAST u v =
    do
        UnifyActions{actionUnifyUnboundToAST} <- M.askEnv <&> envActions
        actionUnifyUnboundToAST u v & infer

unifyUnbounds :: Constraints tag -> Constraints tag -> Unify tag s (Constraints tag)
unifyUnbounds u v =
    do
        UnifyActions{actionUnifyUnbounds} <- M.askEnv <&> envActions
        actionUnifyUnbounds u v & infer

infer :: M.Infer s a -> Unify tag s a
infer = M.localEnv envInfer

runUnify ::
    Monoid (Constraints tag) =>
    (AST tag MetaTypeAST -> AST tag MetaTypeAST -> M.Infer s ()) ->
    Unify tag s a -> M.Infer s a
runUnify f act =
    M.localEnv
    (UnifyEnv UnifyActions
     { actionUnifyASTs = f
     , actionUnifyUnboundToAST = {-# SCC "constraintsPropagate" #-}constraintsPropagate
     , actionUnifyUnbounds = \uCs vCs -> return (uCs `mappend` vCs)
     })
    act

unifyVarAST :: AST tag MetaTypeAST -> MetaVar tag -> Unify tag s ()
unifyVarAST uAst v =
    infer (M.repr v) >>= \case
    (_, Bound vAst) -> unifyASTs uAst vAst
    (vRef, Unbound vCs) ->
        do
            unifyUnboundToAST vCs uAst
            infer $ M.writeRef vRef $ LinkFinal $ Bound uAst

{-# INLINE unifyUnboundToBound #-}
unifyUnboundToBound ::
    MetaVar tag -> Constraints tag -> (MetaVar tag, AST tag MetaTypeAST) ->
    Unify tag s ()
unifyUnboundToBound uRef uCs (vRef, vAst) =
    do
        unifyUnboundToAST uCs vAst
        -- link to the final ref, and not to the direct AST info so we
        -- know to avoid reunify work in future unify calls
        infer $ M.writeRef uRef $ Link vRef

unify :: MetaTypeAST tag -> MetaTypeAST tag -> Unify tag s ()
unify (MetaTypeAST u) (MetaTypeAST v) = unifyASTs u v
unify (MetaTypeAST u) (MetaTypeVar v) = unifyVarAST u v
unify (MetaTypeVar u) (MetaTypeAST v) = unifyVarAST v u
unify (MetaTypeVar u) (MetaTypeVar v) =
    do
        (uRef, ur) <- M.repr u & infer
        (vRef, vr) <- M.repr v & infer
        -- TODO: Choose which to link into which weight/level-wise
        let link a b = M.writeRef a $ Link b
        unless (uRef == vRef) $
            case (ur, vr) of
            (Unbound uCs, Unbound vCs) ->
                do
                    link uRef vRef & infer
                    cs <- unifyUnbounds uCs vCs
                    infer $ M.writeRef vRef $ LinkFinal $ Unbound cs
            (Unbound uCs, Bound vAst) -> unifyUnboundToBound uRef uCs (vRef, vAst)
            (Bound uAst, Unbound vCs) -> unifyUnboundToBound vRef vCs (uRef, uAst)
            (Bound uAst, Bound vAst) ->
                do
                    link uRef vRef & infer
                    unifyASTs uAst vAst

--------------------

unifyTypeVar :: AST 'TypeT MetaTypeAST -> MetaVar 'TypeT -> M.Infer s ()
unifyTypeVar ast var = unifyVarAST ast var & runUnify unifyTypeAST

unifyComposite ::
    IsCompositeTag c => MetaComposite c -> MetaComposite c ->
    M.Infer s ()
unifyComposite u v =
    {-# SCC "unifyComposite" #-}unify u v & runUnify unifyCompositeAST

unifyType :: MetaType -> MetaType -> M.Infer s ()
unifyType u v = {-# SCC "unifyType" #-}unify u v & runUnify unifyTypeAST
