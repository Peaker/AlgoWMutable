{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
module Lamdu.Infer.Monad
    ( Infer
    , Err(..), throwError
    , runInfer
    , repr
    , freshPos, writePos
    , writeRef
    , freshTVar
    , localScope
    , lookupGlobal, lookupLocal
    , instantiate, generalize
    ) where

import           Control.Lens.Operators
import           Control.Monad.ST (ST, runST)
import           Control.Monad.Trans.Class (lift)
import           Control.Monad.Trans.WriterT (WriterT, runWriterT, tell)
import           Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import           Data.RefZone (Zone)
import qualified Data.RefZone as RefZone
import           Data.STRef
import           Data.Set (Set)
import qualified Data.Set as Set
import           Lamdu.Expr.Identifier (Tag(..))
import qualified Lamdu.Expr.Type as Type
import           Lamdu.Expr.Type.Constraints (Constraints(..))
import           Lamdu.Expr.Type.Meta (MetaType, MetaVar(..), MetaTypeAST(..), IsBound(..))
import           Lamdu.Expr.Type.Pure (T(..), TVarName(..))
import           Lamdu.Expr.Type.Scheme (Scheme(..), SchemeBinders(..))
import           Lamdu.Expr.Type.Tag
    ( ASTTag(..), ASTTagEquality(..), IsTag(..)
    , CompositeTagEquality(..) )
import           Lamdu.Expr.Val (Var)
import           Lamdu.Infer.Scope (Scope)
import qualified Lamdu.Infer.Scope as Scope
import           Pretty.Map ()
import           Pretty.Utils (intercalate)
import           Text.PrettyPrint (Doc, (<+>))
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

import           Prelude.Compat

data Err
    = DoesNotUnify Doc Doc
    | VarNotInScope Var
    | InfiniteType
    | DuplicateFields [Tag]
    deriving (Show)

instance Pretty Err where
    pPrint (DoesNotUnify expected got) =
        "expected:" <+> expected <+> "but got:" <+> got
    pPrint (VarNotInScope name) =
        pPrint name <+> "not in scope!"
    pPrint InfiniteType =
        "Infinite type encountered"
    pPrint (DuplicateFields names) =
        "Duplicate fields in record:" <+>
        (intercalate ", " . map pPrint) names

data Env s = Env
    { envFresh :: STRef s Int
    , envZone :: Zone s
    , envScope :: Scope MetaType
    }

newtype Infer s a = Infer
    { unInfer :: Env s -> ST s (Either Err a)
    } deriving (Functor)
instance Applicative (Infer s) where
    {-# INLINE pure #-}
    pure x = Infer $ \_ -> pure (Right x)
    {-# INLINE (<*>) #-}
    Infer f <*> Infer x =
        Infer $ \s -> f s >>= \case
        Left err -> pure (Left err)
        Right fres -> x s >>= \case
            Left err -> pure (Left err)
            Right xres ->
                pure (Right (fres xres))
instance Monad (Infer s) where
    {-# INLINE return #-}
    return = pure
    {-# INLINE (>>=) #-}
    Infer act >>= f = Infer $ \s -> act s >>= \case
        Left err -> pure (Left err)
        Right x -> unInfer (f x) s

runInfer :: Scope MetaType -> (forall s. Infer s a) -> Either Err a
runInfer scope act =
    runST $
    do
        fresh <- newSTRef 0
        zone <- RefZone.new
        unInfer act Env { envFresh = fresh, envZone = zone, envScope = scope }

{-# INLINE askEnv #-}
askEnv :: Infer s (Env s)
askEnv = Infer (return . Right)

{-# INLINE liftST #-}
liftST :: ST s a -> Infer s a
liftST act = Infer $ \_ -> act <&> Right

throwError :: Err -> Infer s a
throwError err = Infer $ \_ -> return $ Left err

{-# INLINE localEnv #-}
localEnv :: (Env s -> Env s) -> Infer s a -> Infer s a
localEnv f (Infer act) = Infer (act . f)

-- TODO: bench inlining of ref operations

newRef :: a -> Infer s (RefZone.Ref a)
newRef x =
    do
        zone <- askEnv <&> envZone
        RefZone.newRef zone x & liftST

readRef :: RefZone.Ref b -> Infer s b
readRef ref =
    do
        zone <- askEnv <&> envZone
        RefZone.readRef zone ref & liftST

writeRef :: RefZone.Ref a -> a -> Infer s ()
writeRef ref val =
    do
        zone <- askEnv <&> envZone
        RefZone.writeRef zone ref val & liftST

writePos :: MetaVar tag -> IsBound tag (MetaTypeAST tag) -> Infer s ()
writePos pos x = writeRef (__unificationPosRef pos) x

{-# INLINE localScope #-}
localScope ::
    (Scope MetaType -> Scope MetaType) ->
    Infer s a -> Infer s a
localScope f = localEnv $ \e -> e { envScope = f (envScope e) }

{-# INLINE askScope #-}
askScope :: Infer s (Scope MetaType)
askScope = askEnv <&> envScope

{-# INLINE lookupLocal #-}
lookupLocal :: Var -> Infer s (Maybe MetaType)
lookupLocal v = askScope <&> Scope.lookupLocal v

{-# INLINE lookupGlobal #-}
lookupGlobal :: Var -> Infer s (Maybe (Scheme 'TypeT))
lookupGlobal v = askScope <&> Scope.lookupGlobal v

nextFresh :: Infer s Int
nextFresh =
    askEnv <&> envFresh >>= \ref ->
    do
        old <- readSTRef ref
        let !new = 1 + old
        writeSTRef ref $! new
        return new
    & liftST

freshPos :: Constraints tag -> Infer s (MetaVar tag)
freshPos cs =
    do
        posName <- nextFresh
        ref <- Unbound cs & newRef
        MetaVar (Set.singleton posName) ref & return

{-# INLINE freshTVar #-}
freshTVar :: Constraints tag -> Infer s (MetaTypeAST tag)
freshTVar cs = freshPos cs <&> MetaTypeVar

instantiate :: forall s tag. IsTag tag => Scheme tag -> Infer s (MetaTypeAST tag)
instantiate (Scheme (SchemeBinders typeVars recordVars sumVars) typ) =
    {-# SCC "instantiate" #-}
    do
        typeUFs <- {-# SCC "instantiate.freshtvs" #-}traverse freshTVar typeVars
        recordUFs <- {-# SCC "instantiate.freshrtvs" #-}traverse freshTVar recordVars
        sumUFs <- {-# SCC "instantiate.freshstvs" #-}traverse freshTVar sumVars
        let go :: IntMap (MetaTypeAST t) -> T t -> Infer s (MetaTypeAST t)
            go binders (TVar (TVarName i)) = return (binders IntMap.! i)
            go _ (T typeAST) =
                Type.ntraverse (go typeUFs) (go recordUFs) (go sumUFs) typeAST
                <&> MetaTypeAST
        {-# SCC "instantiate.go" #-}typ & case tagRefl :: ASTTagEquality tag of
            IsTypeT -> go typeUFs
            IsCompositeT IsRecordC -> go recordUFs
            IsCompositeT IsSumC -> go sumUFs

repr ::
    MetaVar tag ->
    Infer s (MetaVar tag, IsBound tag (Type.AST tag MetaTypeAST))
repr x =
    do
        zone <- askEnv <&> envZone
        let go pos@(MetaVar _ ref) =
                RefZone.readRef zone ref >>= \case
                Unbound uCs -> return (pos, Unbound uCs)
                Bound (MetaTypeAST ast) -> return (pos, Bound ast)
                Bound (MetaTypeVar innerPos) ->
                    do
                        res <- go innerPos
                        -- path compression:
                        RefZone.writeRef zone ref (snd res <&> MetaTypeAST)
                        return res
        liftST $ go x

schemeBindersSingleton :: forall tag. IsTag tag => TVarName tag -> Constraints tag -> SchemeBinders
schemeBindersSingleton (TVarName tvName) cs =
    case tagRefl :: ASTTagEquality tag of
    IsTypeT -> mempty { schemeTypeBinders = binders }
    IsCompositeT IsRecordC -> mempty { schemeRecordBinders = binders }
    IsCompositeT IsSumC -> mempty { schemeSumBinders = binders }
    where
        binders = IntMap.singleton tvName cs

deref ::
    forall s tag. IsTag tag =>
    Set Int -> MetaTypeAST tag -> WriterT SchemeBinders (Infer s) (T tag)
deref visited = \case
    MetaTypeAST ast ->
        ast & Type.ntraverse (deref visited) (deref visited) (deref visited) <&> T
    MetaTypeVar (MetaVar posNames tvRef)
        | posName `Set.member` visited ->
              throwError InfiniteType & lift
        | otherwise ->
            -- TODO: Avoid Infer s monad and use ST directly?
            lift (readRef tvRef) >>= \case
            Unbound cs ->
                do
                    let tvName = TVarName posName
                    tell $ schemeBindersSingleton tvName cs
                    return $ TVar tvName
            Bound meta ->
                deref (Set.insert posName visited) meta
        where
            posName = Set.findMin posNames

generalize :: MetaType -> Infer s (Scheme 'TypeT)
generalize t =
    {-# SCC "generalize" #-}
    deref Set.empty t
    & runWriterT
    <&> uncurry (flip Scheme)