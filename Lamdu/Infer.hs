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
import qualified Data.Map.Strict as Map
import qualified Data.RefZone as RefZone
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Typeable (Typeable)
import           GHC.Exts (inline)
import           GHC.Generics (Generic)
import           Lamdu.Expr.Identifier (Tag)
import           Lamdu.Expr.Type (AST(..))
import           Lamdu.Expr.Type.Constraints (Constraints(..))
import qualified Lamdu.Expr.Type.Constraints as Constraints
import           Lamdu.Expr.Type.Scheme (Scheme)
import           Lamdu.Expr.Type.Tag (IsCompositeTag(..), ASTTag(..))
import           Lamdu.Expr.Val (Body(..))
import qualified Lamdu.Expr.Val as Val
import           Lamdu.Expr.Val.Annotated (AV(..))
import qualified Lamdu.Infer.Deref as Deref
import           Lamdu.Infer.Meta
import           Lamdu.Infer.Monad (Infer)
import qualified Lamdu.Infer.Monad as M
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

type InferAction s a = Scope -> Infer s (Body (AV (Payload, a)), MetaType)

freshMetaTypeVar :: Scope -> Infer s (MetaTypeAST 'TypeT)
freshMetaTypeVar scope =
    MetaVarInfo TypeConstraints (Scope.skolemScope scope)
    & M.freshMetaVar

freshMetaCompositeVar :: Set Tag -> Scope -> Infer s (MetaTypeAST ('CompositeT c))
freshMetaCompositeVar forbidden scope =
    MetaVarInfo constraints (Scope.skolemScope scope)
    & M.freshMetaVar
    where
        constraints = CompositeConstraints (Constraints.Composite forbidden)

inferLeaf :: Val.Leaf -> InferAction s a
inferLeaf leaf scope =
    {-# SCC "inferLeaf" #-}
    case leaf of
    Val.LEmptyRecord ->
        {-# SCC "inferEmptyRecord" #-}
        MetaTypeAST TEmptyComposite & TRecord & MetaTypeAST & return
    Val.LAbsurd ->
        {-# SCC "inferAbsurd" #-}
        do
            res <- freshMetaTypeVar scope
            let emptyVariant = MetaTypeAST TEmptyComposite & TVariant & MetaTypeAST
            TFun emptyVariant res & MetaTypeAST & return
    Val.LLiteral (Val.PrimVal nomId _) ->
        {-# SCC "inferLiteral" #-}
        MetaTypeAST (TInst nomId Map.empty) & return
    Val.LHole -> {-# SCC "inferHole" #-}freshMetaTypeVar scope
    Val.LVar n ->
        {-# SCC "inferVar" #-}
        case Scope.lookupLocal n scope of
        Just typ -> return typ
        Nothing ->
            {-# SCC "inferGlobal" #-}
            case Scope.lookupGlobal n scope of
            Just scheme -> M.instantiate scheme (Scope.skolemScope scope)
            Nothing -> M.throwError $ M.VarNotInScope n
    <&> (,) (Val.BLeaf leaf)

inferLam :: Val.Lam (AV a) -> InferAction s a
inferLam (Val.Lam n body) scope =
    {-# SCC "inferLam" #-}
    do
        nType <- freshMetaTypeVar scope
        (body', resType) <- infer body (Scope.insertLocal n nType scope)
        return (Val.BLam (Val.Lam n body'), TFun nType resType & MetaTypeAST)

inferApp :: Val.Apply (AV a) -> InferAction s a
inferApp (Val.Apply fun arg) scope =
    {-# SCC "inferApp" #-}
    do
        (fun', funTyp) <- infer fun scope
        (arg', argTyp) <- infer arg scope
        -- TODO: Maybe a simple unify, if inlined, will be as fast?
        resTyp <-
            case funTyp of
            MetaTypeVar ref ->
                do
                    resTyp <- freshMetaTypeVar scope
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
inferRecExtend (Val.RecExtend name val rest) scope =
    {-# SCC "inferRecExtend" #-}
    do
        (rest', restTyp) <- infer rest scope
        restRecordTyp <-
            case restTyp of
            MetaTypeVar ref ->
                do
                    unknownRestFields <-
                        freshMetaCompositeVar (Set.singleton name) scope
                    -- TODO (Optimization): ref known to be unbound
                    unifyTypeVar ref (TRecord unknownRestFields)
                    return unknownRestFields
            MetaTypeAST (TRecord restRecordTyp) ->
                do
                    propagateConstraint name scope restRecordTyp
                    return restRecordTyp
            MetaTypeAST t ->
                M.DoesNotUnify (pPrint t) "Record type" & M.throwError
        (val', valTyp) <- infer val scope
        let typ =
                TCompositeExtend name valTyp restRecordTyp
                & MetaTypeAST
                & TRecord & MetaTypeAST
        return (Val.BRecExtend (Val.RecExtend name val' rest'), typ)
    where

propagateConstraint :: IsCompositeTag c => Tag -> Scope -> MetaComposite c -> Infer s ()
propagateConstraint tagName scope =
    \case
    MetaTypeAST x -> toBound x
    MetaTypeVar ref ->
        M.repr ref >>= \case
        (_, Bound ast) -> toBound ast
        (vRef, Unbound (MetaVarInfo (CompositeConstraints cs) skolemScope)) ->
            M.writeRef vRef $ LinkFinal $ Unbound $ MetaVarInfo
            { metaVarConstraints =
                    cs
                    & Constraints.forbiddenFields %~ Set.insert tagName
                    & CompositeConstraints
            , metaVarSkolemScope = skolemScope
            }
    where
        toBound (TSkolem tv) =
            do
                CompositeConstraints (Constraints.Composite oldConstraints) <-
                    M.lookupSkolem tv (Scope.skolemScope scope)
                unless (tagName `Set.member` oldConstraints) $
                    M.ConstraintUnavailable tagName ("in skolem" <+> pPrint tv)
                    & M.throwError
        toBound TEmptyComposite = return ()
        toBound (TCompositeExtend fieldTag _ restTyp)
            | fieldTag == tagName = M.DuplicateFields [tagName] & M.throwError
            | otherwise = propagateConstraint tagName scope restTyp

inferCase :: Val.Case (AV a) -> InferAction s a
inferCase (Val.Case name handler restHandler) scope =
    {-# SCC "inferCase" #-}
    do
        resType <- freshMetaTypeVar scope
        let toResType x = TFun x resType & MetaTypeAST

        fieldType <- freshMetaTypeVar scope

        (handler', handlerTyp) <- infer handler scope
        (restHandler', restHandlerTyp) <- infer restHandler scope

        variantTail <- freshMetaCompositeVar (Set.singleton name) scope

        let expectedHandlerTyp = toResType fieldType
        unifyType expectedHandlerTyp handlerTyp

        let expectedRestHandlerType = TVariant variantTail & MetaTypeAST & toResType
        unifyType expectedRestHandlerType restHandlerTyp

        let typ =
                TCompositeExtend name fieldType variantTail
                & MetaTypeAST & TVariant & MetaTypeAST & toResType
        return (Val.BCase (Val.Case name handler' restHandler'), typ)

inferGetField :: Val.GetField (AV a) -> InferAction s a
inferGetField (Val.GetField val name) scope =
    {-# SCC "inferGetField" #-}
    do
        resTyp <- freshMetaTypeVar scope
        (val', valTyp) <- infer val scope
        expectedValTyp <-
            freshMetaCompositeVar (Set.singleton name) scope
            <&> TCompositeExtend name resTyp
            <&> MetaTypeAST
            <&> TRecord <&> MetaTypeAST
        unifyType expectedValTyp valTyp
        return (Val.BGetField (Val.GetField val' name), resTyp)

inferInject :: Val.Inject (AV a) -> InferAction s a
inferInject (Val.Inject name val) scope =
    {-# SCC "inferInject" #-}
    do
        (val', valTyp) <- infer val scope
        typ <-
            freshMetaCompositeVar (Set.singleton name) scope
            <&> TCompositeExtend name valTyp
            <&> MetaTypeAST
            <&> TVariant <&> MetaTypeAST
        return (Val.BInject (Val.Inject name val'), typ)

inferFromNom :: Val.Nom (AV a) -> InferAction s a
inferFromNom (Val.Nom n val) scope =
    do
        (val', valTyp) <- infer val scope
        -- TODO: Optimization: give valTyp (which should be a TInst)
        -- directly to instantiateFromNom, which can directly work
        -- with the params instead of creating metavars and unifying
        -- with them immediately after
        (nomTypeParams, innerTyp) <-
            M.lookupNominal n scope
            >>= InferNominal.instantiateFromNom (Scope.skolemScope scope) n
        let tInstType = TInst n nomTypeParams & MetaTypeAST
        unifyType tInstType valTyp
        return (Val.BFromNom (Val.Nom n val'), innerTyp)

inferToNom :: Val.Nom (AV a) -> InferAction s a
inferToNom (Val.Nom n val) scope =
    do
        (nomTypeParams, (innerBinders, innerTyp)) <-
            M.lookupNominal n scope
            >>= InferNominal.instantiateToNom (Scope.skolemScope scope) n
        scope' <- M.extendSkolemScope innerBinders scope
        (val', valTyp) <- infer val scope'
        unifyType innerTyp valTyp
        let typ =
                TInst n nomTypeParams
                & MetaTypeAST
        return (Val.BToNom (Val.Nom n val'), typ)

infer :: AV a -> Scope -> Infer s (AV (Payload, a), MetaType)
infer (AV pl val) scope =
    {-# SCC "infer" #-}
    scope
    & case val of
    Val.BLeaf x      -> inferLeaf x
    Val.BLam x       -> inferLam x
    Val.BApp x       -> inferApp x
    Val.BRecExtend x -> inferRecExtend x
    Val.BGetField x  -> inferGetField x
    Val.BInject x    -> inferInject x
    Val.BFromNom x   -> inferFromNom x
    Val.BToNom x     -> inferToNom x
    Val.BCase x      -> inferCase x
    <&> annotate
    where
        annotate (val', typ) = (AV (Payload typ scope, pl) val', typ)

inferScheme :: AV a -> Scope -> M.Infer s (AV (Payload, a), Scheme 'TypeT)
inferScheme x scope =
    {-# SCC "inferScheme" #-}
    infer x scope >>= Deref.run . inline _2 Deref.generalize
