{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
module Type.Infer
    ( Infer, M.runInfer, inferScheme, infer
    ) where

import           Control.Lens.Operators
import           Control.Lens.Tuple
import qualified Data.Map as Map
import qualified Data.Set as Set
import           GHC.Exts (inline)
import           Pretty.Map ()
import           Text.PrettyPrint.HughesPJClass (Pretty(..))
import           Type (Type, AST(..))
import           Type.Constraints (Constraints(..))
import           Type.Infer.Monad (Infer)
import qualified Type.Infer.Monad as M
import           Type.Infer.Scope (Scope)
import qualified Type.Infer.Scope as Scope
import           Type.Infer.Unify
import           Type.Meta
import           Type.Scheme (Scheme)
import           Type.Tag (ASTTag(..))
import qualified Val
import           Val (Val(..))
import           Val.Annotated (AV(..))
import           Val.Pure (V(..))

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
            res <- M.freshTVar TypeConstraints
            let emptySum = MetaTypeAST TEmptyComposite & TSum & MetaTypeAST
            TFun emptySum res & MetaTypeAST & return
    Val.LInt _ ->
        {-# SCC "inferInt" #-}
        MetaTypeAST int & return
    Val.LHole ->
        {-# SCC "inferHole" #-}
        M.freshTVar TypeConstraints
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
        nType <- M.freshTVar TypeConstraints
        (body', resType) <- infer body & M.localScope (Scope.insertLocal n nType)
        TFun nType resType & MetaTypeAST
            & inferRes (Val.BLam (Val.Abs n body')) & return

inferApp :: Val.App V -> Infer s InferResult
inferApp (Val.App fun arg) =
    {-# SCC "inferApp" #-}
    do
        (fun', funTyp) <- infer fun
        (arg', argTyp) <- infer arg
        resTyp <-
            case funTyp of
            MetaTypeVar pos ->
                do
                    resTyp <- M.freshTVar TypeConstraints
                    unifyVarAST unifyTypeAST (TFun argTyp resTyp) pos
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
            MetaTypeVar pos ->
                do
                    unknownRestFields <-
                        M.freshTVar $ CompositeConstraints $
                        Set.singleton name
                    -- TODO (Optimization): pos known to be unbound
                    unifyVarAST unifyTypeAST (TRecord unknownRestFields) pos
                    return unknownRestFields
            MetaTypeAST (TRecord restRecordTyp) ->
                do
                    propagateConstraint restRecordTyp
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
        propagateConstraint (MetaTypeAST x) = propagateConstraintBound x
        propagateConstraint (MetaTypeVar pos) =
            M.repr pos >>= \case
            (_, Bound ast) -> propagateConstraintBound ast
            (vPos, Unbound (CompositeConstraints cs)) ->
                M.writePos vPos $ Unbound $ CompositeConstraints $
                Set.insert name cs
        propagateConstraintBound TEmptyComposite = return ()
        propagateConstraintBound (TCompositeExtend fieldTag _ restTyp)
            | fieldTag == name = M.DuplicateFields [name] & M.throwError
            | otherwise = propagateConstraint restTyp

inferCase :: Val.Case V -> Infer s InferResult
inferCase (Val.Case name handler restHandler) =
    {-# SCC "inferCase" #-}
    do
        resType <- M.freshTVar TypeConstraints
        let toResType x = TFun x resType & MetaTypeAST

        fieldType <- M.freshTVar TypeConstraints

        (handler', handlerTyp) <- infer handler
        (restHandler', restHandlerTyp) <- infer restHandler

        sumTail <- M.freshTVar $ CompositeConstraints $ Set.singleton name

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
        resTyp <- M.freshTVar TypeConstraints
        (val', valTyp) <- infer val
        expectedValTyp <-
            M.freshTVar (CompositeConstraints (Set.singleton name))
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
        M.freshTVar (CompositeConstraints (Set.singleton name))
            <&> TCompositeExtend name valTyp
            <&> MetaTypeAST
            <&> TSum <&> MetaTypeAST
            <&> inferRes (Val.BInject (Val.Inject name val'))

infer :: V -> Infer s InferResult
infer (V v) =
    {-# SCC "infer" #-}
    case v of
    Val.BLeaf x -> inferLeaf x
    Val.BLam x -> inferLam x
    Val.BApp x -> inferApp x
    Val.BRecExtend x -> inferRecExtend x
    Val.BGetField x -> inferGetField x
    Val.BInject x -> inferInject x
    Val.BCase x -> inferCase x

inferScheme :: Scope MetaType -> V -> Either M.Err (AV MetaType, Scheme 'TypeT)
inferScheme scope x =
    {-# SCC "inferScheme" #-}
    M.runInfer scope $ infer x >>= inline _2 M.generalize
