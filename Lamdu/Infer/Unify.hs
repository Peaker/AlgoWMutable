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
    where

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
flatten (MetaTypeVar pos) =
    M.repr pos >>= \case
    (_, Unbound cs) -> return $ FlatComposite Map.empty $ CompositeTailOpen pos cs
    (_, Bound ast) -> flattenVal ast

unflatten :: IsCompositeTag c => FlatComposite c -> MetaComposite c
unflatten (FlatComposite fields tail) =
    {-# SCC "unflatten" #-}Map.toList fields & go
    where
        go [] = case tail of
            CompositeTailClosed -> MetaTypeAST TEmptyComposite
            CompositeTailOpen pos _ -> MetaTypeVar pos
        go ((name, typ):fs) =
            go fs & TCompositeExtend name typ & MetaTypeAST

prettyFieldNames :: Map Tag a -> Doc
prettyFieldNames = intercalate " " . map pPrint . Map.keys

{-# INLINE unifyCompositesClosedClosed #-}
unifyCompositesClosedClosed :: CompositeFields -> CompositeFields -> M.Infer s ()
unifyCompositesClosedClosed uFields vFields
    | Map.keysSet uFields == Map.keysSet vFields = return ()
    | otherwise =
          M.throwError $
          M.DoesNotUnify
          ("Record fields:" <+> prettyFieldNames uFields)
          ("Record fields:" <+> prettyFieldNames vFields)

flatConstraintsCheck :: Constraints ('CompositeT c) -> FlatComposite c -> M.Infer s ()
flatConstraintsCheck outerConstraints@(CompositeConstraints outerDisallowed) flatComposite =
    do
        unless (Set.null duplicates) $ M.throwError $ M.DuplicateFields $
            Set.toList duplicates
        case innerTail of
            CompositeTailClosed -> return ()
            CompositeTailOpen (MetaVar ref) innerConstraints ->
                M.writeRef ref $ LinkFinal $ Unbound $ outerConstraints `mappend` innerConstraints
    where
        duplicates = Set.intersection (Map.keysSet innerFields) outerDisallowed
        FlatComposite innerFields innerTail = flatComposite

constraintsCheck ::
    Constraints tag -> AST tag MetaTypeAST -> M.Infer s ()
constraintsCheck TypeConstraints _ = return ()
constraintsCheck cs@CompositeConstraints{} inner =
    ({-# SCC "constraintsCheck.flatten" #-}flattenVal inner) >>= flatConstraintsCheck cs

writeCompositeTail ::
    IsCompositeTag c =>
    (MetaVar ('CompositeT c), Constraints ('CompositeT c)) ->
    FlatComposite c -> M.Infer s ()
writeCompositeTail (pos, cs) composite =
    do
        {-# SCC "flatConstraintsCheck" #-}flatConstraintsCheck cs composite
        M.writePos pos $ case unflatten composite of
            MetaTypeAST ast -> LinkFinal $ Bound ast
            MetaTypeVar var -> Link var

{-# INLINE unifyCompositesOpenClosed #-}
unifyCompositesOpenClosed ::
    IsCompositeTag c =>
    (MetaVar ('CompositeT c), Constraints ('CompositeT c), CompositeFields) ->
    CompositeFields -> M.Infer s ()
unifyCompositesOpenClosed (openTailPos, openConstraints, openFields) closedFields
    | Map.null uniqueOpenFields =
          writeCompositeTail (openTailPos, openConstraints) $
          FlatComposite uniqueClosedFields CompositeTailClosed
    | otherwise =
          M.throwError $
          M.DoesNotUnify
          ("Record with at least fields:" <+> prettyFieldNames openFields)
          ("Record fields:" <+> prettyFieldNames closedFields)
    where
        uniqueOpenFields = openFields `Map.difference` closedFields
        uniqueClosedFields = closedFields `Map.difference` openFields

{-# INLINE unifyCompositesOpenOpen #-}
unifyCompositesOpenOpen ::
    IsCompositeTag c =>
    (MetaVar ('CompositeT c), Constraints ('CompositeT c), CompositeFields) ->
    (MetaVar ('CompositeT c), Constraints ('CompositeT c), CompositeFields) ->
    M.Infer s ()
unifyCompositesOpenOpen (uPos, uCs, uFields) (vPos, vCs, vFields) =
    do
        commonRest <- M.freshPos cs <&> (`CompositeTailOpen` cs)
        writeCompositeTail (uPos, uCs) $ FlatComposite uniqueVFields commonRest
        writeCompositeTail (vPos, vCs) $ FlatComposite uniqueUFields commonRest
    where
        cs = uCs `mappend` vCs
        uniqueUFields = uFields `Map.difference` vFields
        uniqueVFields = vFields `Map.difference` uFields

unifyComposite ::
    IsCompositeTag c => MetaComposite c -> MetaComposite c ->
    M.Infer s ()
unifyComposite = {-# SCC "unifyComposite" #-}unify unifyCompositeAST

unifyType :: MetaType -> MetaType -> M.Infer s ()
unifyType = {-# SCC "unifyType" #-}unify unifyTypeAST

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
                {-# SCC "unifyCompositesClosedClosed" #-}unifyCompositesClosedClosed uFields vFields
            (CompositeTailOpen uPos uCs, CompositeTailClosed) ->
                {-# SCC "unifyCompositesOpenClosed" #-}unifyCompositesOpenClosed (uPos, uCs, uFields) vFields
            (CompositeTailClosed, CompositeTailOpen vPos vCs) ->
                {-# SCC "unifyCompositesOpenClosed" #-}unifyCompositesOpenClosed (vPos, vCs, vFields) uFields
            (CompositeTailOpen uPos uCs, CompositeTailOpen vPos vCs) ->
                {-# SCC "unifyCompositesOpenOpen" #-}unifyCompositesOpenOpen (uPos, uCs, uFields) (vPos, vCs, vFields)
        -- We intersect-unify AFTER unifying the composite shapes, so
        -- we know the flat composites are accurate
        Map.intersectionWith unifyType uFields vFields
            & sequenceA_

unify ::
    (Monoid (Constraints tag)) =>
    (AST tag MetaTypeAST ->
     AST tag MetaTypeAST -> M.Infer s ()) ->
    MetaTypeAST tag -> MetaTypeAST tag -> M.Infer s ()
unify f (MetaTypeAST u) (MetaTypeAST v) = f u v
unify f (MetaTypeAST u) (MetaTypeVar v) = unifyVarAST f u v
unify f (MetaTypeVar u) (MetaTypeAST v) = unifyVarAST f v u
unify f (MetaTypeVar u) (MetaTypeVar v) =
    do
        (uPos@(MetaVar uRef), ur) <- M.repr u
        (vPos@(MetaVar vRef), vr) <- M.repr v
        -- TODO: Choose which to link into which weight/level-wise
        let link a b = M.writePos a $ Link b
        unless (uRef == vRef) $
            case (ur, vr) of
            (Unbound uCs, Unbound vCs) ->
                do
                    link uPos vPos
                    M.writeRef vRef $ LinkFinal $ Unbound $ uCs `mappend` vCs
            (Unbound uCs, Bound vAst) -> unifyUnbound uPos uCs vAst
            (Bound uAst, Unbound vCs) -> unifyUnbound vPos vCs uAst
            (Bound uAst, Bound vAst) ->
                do
                    link uPos vPos
                    f uAst vAst

unifyUnbound ::
    MetaVar tag -> Constraints tag -> AST tag MetaTypeAST ->
    M.Infer s ()
unifyUnbound pos cs ast =
    do
        {-# SCC "constraintsCheck" #-}constraintsCheck cs ast
        M.writePos pos $ LinkFinal $ Bound ast

unifyVarAST ::
    (Monoid (Constraints tag)) =>
    (AST tag MetaTypeAST ->
     AST tag MetaTypeAST -> M.Infer s ()) ->
    AST tag MetaTypeAST -> MetaVar tag -> M.Infer s ()
unifyVarAST f uAst v =
    M.repr v >>= \case
    (_, Bound vAst) -> f uAst vAst
    (vPos, Unbound vCs) -> unifyUnbound vPos vCs uAst

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
