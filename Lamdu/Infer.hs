{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
module Lamdu.Infer
    ( Infer, infer, inferScheme
    , Scope, RefZone.Frozen
    , M.Context, M.emptyContext
    , M.runInfer

    , MetaType, M.generalize, M.deref, M.runDeref
    ) where

import           Control.Lens.Operators
import           Control.Lens.Tuple
import           Control.Monad (unless)
import qualified Data.Map as Map
import qualified Data.RefZone as RefZone
import qualified Data.Set as Set
import           GHC.Exts (inline)
import           Lamdu.Expr.Identifier (Tag)
import           Lamdu.Expr.Type (Type, AST(..))
import           Lamdu.Expr.Type.Constraints (Constraints(..))
import           Lamdu.Expr.Type.Scheme (Scheme)
import           Lamdu.Expr.Type.Tag (IsCompositeTag(..), ASTTag(..))
import           Lamdu.Expr.Val (Val(..))
import qualified Lamdu.Expr.Val as Val
import           Lamdu.Expr.Val.Annotated (AV(..))
import           Lamdu.Expr.Val.Pure (V(..))
import           Lamdu.Infer.Meta
import           Lamdu.Infer.Monad (Infer)
import qualified Lamdu.Infer.Monad as M
import qualified Lamdu.Infer.Nominal as InferNominal
import           Lamdu.Infer.Scope (Scope)
import qualified Lamdu.Infer.Scope as Scope
import           Lamdu.Infer.Unify
import           Pretty.Map ()
import           Text.PrettyPrint ((<+>))
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

import           Prelude.Compat

type InferResult = (AV MetaType, MetaType)

int :: Type ast
int = TInst "Int" Map.empty

inferRes :: Val (AV MetaType) -> MetaType -> (AV MetaType, MetaType)
inferRes val typ = (AV typ val, typ)

inferLeaf :: Val.Leaf -> Infer s InferResult
inferLeaf leaf =
    {-# SCC "inferLeaf" #-}
    case leaf of
    Val.LEmptyRecord ->
        {-# SCC "inferEmptyRecord" #-}
        MetaTypeAST TEmptyComposite & TRecord & MetaTypeAST & return
    Val.LAbsurd ->
        {-# SCC "inferAbsurd" #-}
        do
            res <- M.freshMetaVar TypeConstraints
            let emptySum = MetaTypeAST TEmptyComposite & TSum & MetaTypeAST
            TFun emptySum res & MetaTypeAST & return
    Val.LInt _ ->
        {-# SCC "inferInt" #-}
        MetaTypeAST int & return
    Val.LHole ->
        {-# SCC "inferHole" #-}
        M.freshMetaVar TypeConstraints
    Val.LVar n ->
        {-# SCC "inferVar" #-}
        M.lookupLocal n >>= \case
        Just typ -> return typ
        Nothing ->
            {-# SCC "inferGlobal" #-}
            M.lookupGlobal n >>= \case
            Just scheme -> M.instantiate scheme
            Nothing -> M.throwError $ M.VarNotInScope n
    <&> inferRes (Val.BLeaf leaf)

inferLam :: Val.Abs V -> Infer s InferResult
inferLam (Val.Abs n body) =
    {-# SCC "inferLam" #-}
    do
        nType <- M.freshMetaVar TypeConstraints
        (body', resType) <- infer body & M.localScope (Scope.insertLocal n nType)
        TFun nType resType & MetaTypeAST
            & inferRes (Val.BLam (Val.Abs n body')) & return

inferApp :: Val.App V -> Infer s InferResult
inferApp (Val.App fun arg) =
    {-# SCC "inferApp" #-}
    do
        (fun', funTyp) <- infer fun
        (arg', argTyp) <- infer arg
        -- TODO: Maybe a simple unify, if inlined, will be as fast?
        resTyp <-
            case funTyp of
            MetaTypeVar ref ->
                do
                    resTyp <- M.freshMetaVar TypeConstraints
                    unifyTypeVar ref (TFun argTyp resTyp)
                    return resTyp
            MetaTypeAST (TFun paramTyp resTyp) ->
                do
                    unifyType paramTyp argTyp
                    return resTyp
            MetaTypeAST t ->
                M.DoesNotUnify (pPrint t) "Function type" & M.throwError
        inferRes (Val.BApp (Val.App fun' arg')) resTyp & return

inferRecExtend :: Val.RecExtend V -> Infer s InferResult
inferRecExtend (Val.RecExtend name val rest) =
    {-# SCC "inferRecExtend" #-}
    do
        (rest', restTyp) <- infer rest
        restRecordTyp <-
            case restTyp of
            MetaTypeVar ref ->
                do
                    unknownRestFields <-
                        M.freshMetaVar $ CompositeConstraints $
                        Set.singleton name
                    -- TODO (Optimization): ref known to be unbound
                    unifyTypeVar ref (TRecord unknownRestFields)
                    return unknownRestFields
            MetaTypeAST (TRecord restRecordTyp) ->
                do
                    propagateConstraint name restRecordTyp
                    return restRecordTyp
            MetaTypeAST t ->
                M.DoesNotUnify (pPrint t) "Record type" & M.throwError
        (val', valTyp) <- infer val
        TCompositeExtend name valTyp restRecordTyp
            & MetaTypeAST
            & TRecord & MetaTypeAST
            & inferRes (Val.BRecExtend (Val.RecExtend name val' rest'))
            & return
    where

propagateConstraint :: IsCompositeTag c => Tag -> MetaComposite c -> Infer s ()
propagateConstraint tagName =
    \case
    MetaTypeAST x -> toBound x
    MetaTypeVar ref ->
        M.repr ref >>= \case
        (_, Bound ast) -> toBound ast
        (vRef, Unbound (MetaVarInfo (CompositeConstraints cs) skolemScope)) ->
            M.writeRef vRef $ LinkFinal $ Unbound $ MetaVarInfo
            { metaVarConstraints = CompositeConstraints $ Set.insert tagName cs
            , metaVarSkolemScope = skolemScope
            }
    where
        toBound (TSkolem tv) =
            do
                CompositeConstraints oldConstraints <- M.lookupSkolem tv
                unless (tagName `Set.member` oldConstraints) $
                    M.ConstraintUnavailable tagName ("in skolem" <+> pPrint tv)
                    & M.throwError
        toBound TEmptyComposite = return ()
        toBound (TCompositeExtend fieldTag _ restTyp)
            | fieldTag == tagName = M.DuplicateFields [tagName] & M.throwError
            | otherwise = propagateConstraint tagName restTyp

inferCase :: Val.Case V -> Infer s InferResult
inferCase (Val.Case name handler restHandler) =
    {-# SCC "inferCase" #-}
    do
        resType <- M.freshMetaVar TypeConstraints
        let toResType x = TFun x resType & MetaTypeAST

        fieldType <- M.freshMetaVar TypeConstraints

        (handler', handlerTyp) <- infer handler
        (restHandler', restHandlerTyp) <- infer restHandler

        sumTail <- M.freshMetaVar $ CompositeConstraints $ Set.singleton name

        let expectedHandlerTyp = toResType fieldType
        unifyType expectedHandlerTyp handlerTyp

        let expectedRestHandlerType = TSum sumTail & MetaTypeAST & toResType
        unifyType expectedRestHandlerType restHandlerTyp

        TCompositeExtend name fieldType sumTail
            & MetaTypeAST & TSum & MetaTypeAST & toResType
            & inferRes (Val.BCase (Val.Case name handler' restHandler'))
            & return

inferGetField :: Val.GetField V -> Infer s InferResult
inferGetField (Val.GetField val name) =
    {-# SCC "inferGetField" #-}
    do
        resTyp <- M.freshMetaVar TypeConstraints
        (val', valTyp) <- infer val
        expectedValTyp <-
            M.freshMetaVar (CompositeConstraints (Set.singleton name))
            <&> TCompositeExtend name resTyp
            <&> MetaTypeAST
            <&> TRecord <&> MetaTypeAST
        unifyType expectedValTyp valTyp
        inferRes (Val.BGetField (Val.GetField val' name)) resTyp & return

inferInject :: Val.Inject V -> Infer s InferResult
inferInject (Val.Inject name val) =
    {-# SCC "inferInject" #-}
    do
        (val', valTyp) <- infer val
        M.freshMetaVar (CompositeConstraints (Set.singleton name))
            <&> TCompositeExtend name valTyp
            <&> MetaTypeAST
            <&> TSum <&> MetaTypeAST
            <&> inferRes (Val.BInject (Val.Inject name val'))

inferFromNom :: Val.Nom V -> Infer s InferResult
inferFromNom (Val.Nom n val) =
    do
        (val', valTyp) <- infer val
        -- TODO: Optimization: give valTyp (which should be a TInst)
        -- directly to instantiateFromNom, which can directly work
        -- with the params instead of creating metavars and unifying
        -- with them immediately after
        (nomTypeParams, innerTyp) <-
            M.lookupNominal n >>= InferNominal.instantiateFromNom n
        let tInstType = TInst n nomTypeParams & MetaTypeAST
        unifyType tInstType valTyp
        inferRes (Val.BFromNom (Val.Nom n val')) innerTyp & return

inferToNom :: Val.Nom V -> Infer s InferResult
inferToNom (Val.Nom n val) =
    do
        (nomTypeParams, (innerBinders, innerTyp)) <-
            M.lookupNominal n >>= InferNominal.instantiateToNom n
        val' <-
            do
                (val', valTyp) <- infer val
                unifyType innerTyp valTyp
                return val'
            & M.withSkolemScope innerBinders
        TInst n nomTypeParams
            & MetaTypeAST
            & inferRes (Val.BToNom (Val.Nom n val'))
            & return

infer :: V -> Infer s InferResult
infer (V v) =
    {-# SCC "infer" #-}
    case v of
    Val.BLeaf x      -> inferLeaf x
    Val.BLam x       -> inferLam x
    Val.BApp x       -> inferApp x
    Val.BRecExtend x -> inferRecExtend x
    Val.BGetField x  -> inferGetField x
    Val.BInject x    -> inferInject x
    Val.BFromNom x   -> inferFromNom x
    Val.BToNom x     -> inferToNom x
    Val.BCase x      -> inferCase x

inferScheme :: V -> M.Infer s (AV MetaType, Scheme 'TypeT)
inferScheme x =
    {-# SCC "inferScheme" #-}
    infer x >>= inline _2 M.generalize
