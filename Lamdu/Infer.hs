{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
module Lamdu.Infer
    ( Infer, infer, inferScheme
    , unifyType
    , Payload(..), plType, plScope
    , Scope, RefZone.Frozen
    , M.Context, M.emptyContext
    , M.runInfer
    , M.Err(..)

    , MetaType
    ) where

import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Lens.Tuple
import           Control.Monad (unless)
import qualified Data.Map as Map
import qualified Data.RefZone as RefZone
import qualified Data.Set as Set
import           Data.Typeable (Typeable)
import           GHC.Exts (inline)
import           GHC.Generics (Generic)
import           Lamdu.Expr.Identifier (Tag)
import           Lamdu.Expr.Type (AST(..))
import           Lamdu.Expr.Type.Constraints (Constraints(..))
import           Lamdu.Expr.Type.Scheme (Scheme)
import           Lamdu.Expr.Type.Tag (IsCompositeTag(..), ASTTag(..))
import           Lamdu.Expr.Val (Body(..))
import qualified Lamdu.Expr.Val as Val
import           Lamdu.Expr.Val.Annotated (AV(..))
import           Lamdu.Infer.Meta
import           Lamdu.Infer.Monad (Infer)
import qualified Lamdu.Infer.Monad as M
import qualified Lamdu.Infer.Deref as Deref
import qualified Lamdu.Infer.Nominal as InferNominal
import           Lamdu.Infer.Scope (Scope)
import qualified Lamdu.Infer.Scope as Scope
import           Lamdu.Infer.Unify (unifyType, unifyTypeVar)
import           Pretty.Map ()
import           Text.PrettyPrint ((<+>))
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

import           Prelude.Compat

data Payload = Payload
    { _plType :: MetaType
    , _plScope :: Scope
    } deriving (Generic, Typeable)

Lens.makeLenses ''Payload

type InferAction s a = Infer s (Body (AV (Payload, a)), MetaType)

inferLeaf :: Val.Leaf -> InferAction s a
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
    Val.LLiteral (Val.PrimVal nomId _) ->
        {-# SCC "inferLiteral" #-}
        MetaTypeAST (TInst nomId Map.empty) & return
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
    <&> (,) (Val.BLeaf leaf)

inferLam :: Val.Abs (AV a) -> InferAction s a
inferLam (Val.Abs n body) =
    {-# SCC "inferLam" #-}
    do
        nType <- M.freshMetaVar TypeConstraints
        (body', resType) <- infer body & M.localScope (Scope.insertLocal n nType)
        return (Val.BLam (Val.Abs n body'), TFun nType resType & MetaTypeAST)

inferApp :: Val.Apply (AV a) -> InferAction s a
inferApp (Val.Apply fun arg) =
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
        return (Val.BApp (Val.Apply fun' arg'), resTyp)

inferRecExtend :: Val.RecExtend (AV a) -> InferAction s a
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
        let typ =
                TCompositeExtend name valTyp restRecordTyp
                & MetaTypeAST
                & TRecord & MetaTypeAST
        return (Val.BRecExtend (Val.RecExtend name val' rest'), typ)
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

inferCase :: Val.Case (AV a) -> InferAction s a
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

        let typ =
                TCompositeExtend name fieldType sumTail
                & MetaTypeAST & TSum & MetaTypeAST & toResType
        return (Val.BCase (Val.Case name handler' restHandler'), typ)

inferGetField :: Val.GetField (AV a) -> InferAction s a
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
        return (Val.BGetField (Val.GetField val' name), resTyp)

inferInject :: Val.Inject (AV a) -> InferAction s a
inferInject (Val.Inject name val) =
    {-# SCC "inferInject" #-}
    do
        (val', valTyp) <- infer val
        typ <-
            M.freshMetaVar (CompositeConstraints (Set.singleton name))
            <&> TCompositeExtend name valTyp
            <&> MetaTypeAST
            <&> TSum <&> MetaTypeAST
        return (Val.BInject (Val.Inject name val'), typ)

inferFromNom :: Val.Nom (AV a) -> InferAction s a
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
        return (Val.BFromNom (Val.Nom n val'), innerTyp)

inferToNom :: Val.Nom (AV a) -> InferAction s a
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
        let typ =
                TInst n nomTypeParams
                & MetaTypeAST
        return (Val.BToNom (Val.Nom n val'), typ)

infer :: AV a -> Infer s (AV (Payload, a), MetaType)
infer (AV pl val) =
    {-# SCC "infer" #-}
    case val of
    Val.BLeaf x      -> inferLeaf x
    Val.BLam x       -> inferLam x
    Val.BApp x       -> inferApp x
    Val.BRecExtend x -> inferRecExtend x
    Val.BGetField x  -> inferGetField x
    Val.BInject x    -> inferInject x
    Val.BFromNom x   -> inferFromNom x
    Val.BToNom x     -> inferToNom x
    Val.BCase x      -> inferCase x
    >>= annotate
    where
        annotate (val', typ) =
            do
                scope <- M.askEnv <&> M.envScope
                return (AV (Payload typ scope, pl) val', typ)

inferScheme :: AV a -> M.Infer s (AV (Payload, a), Scheme 'TypeT)
inferScheme x =
    {-# SCC "inferScheme" #-}
    infer x >>= inline _2 Deref.generalize
