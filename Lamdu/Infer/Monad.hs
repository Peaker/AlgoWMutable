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
    , freshRef
    , writeRef
    , freshMetaVar
    , localScope
    , lookupGlobal, lookupLocal
    , instantiate, generalize
    ) where

import           Control.Lens (Lens')
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Lens.Tuple
import           Control.Monad (when)
import qualified Control.Monad.RSS as RSS
import           Control.Monad.ST (ST, runST)
import           Control.Monad.Trans.Class (lift)
import           Control.Monad.Trans.RSS (RSST, runRSST)
import           Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import           Data.RefZone (Zone)
import qualified Data.RefZone as RefZone
import           Data.RefZone.RefMap (RefMap)
import qualified Data.RefZone.RefMap as RefMap
import           Data.RefZone.RefSet (RefSet)
import qualified Data.RefZone.RefSet as RefSet
import           Data.STRef
import           Lamdu.Expr.Identifier (Tag(..))
import qualified Lamdu.Expr.Type as Type
import           Lamdu.Expr.Type.Constraints (Constraints(..))
import           Lamdu.Expr.Type.Meta
    ( MetaType, MetaVar, MetaTypeAST(..), Link(..), Final(..) )
import           Lamdu.Expr.Type.Pure (T(..), TVarName(..))
import           Lamdu.Expr.Type.Scheme (Scheme(..), SchemeBinders(..))
import           Lamdu.Expr.Type.Tag
    ( ASTTag(..), ASTTagEquality(..), IsTag(..)
    , CompositeTagEquality(..), RecordT, SumT )
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

{-# INLINE newRef #-}
newRef :: a -> Infer s (RefZone.Ref a)
newRef x =
    do
        zone <- askEnv <&> envZone
        RefZone.newRef zone x & liftST

{-# INLINE writeRef #-}
writeRef :: RefZone.Ref a -> a -> Infer s ()
writeRef ref val =
    do
        zone <- askEnv <&> envZone
        RefZone.writeRef zone ref val & liftST

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

{-# INLINE freshRef #-}
freshRef :: Constraints tag -> Infer s (MetaVar tag)
freshRef cs = Unbound cs & LinkFinal & newRef

{-# INLINE freshMetaVar #-}
freshMetaVar :: Constraints tag -> Infer s (MetaTypeAST tag)
freshMetaVar cs = freshRef cs <&> MetaTypeVar

instantiate :: forall s tag. IsTag tag => Scheme tag -> Infer s (MetaTypeAST tag)
instantiate (Scheme (SchemeBinders typeVars recordVars sumVars) typ) =
    {-# SCC "instantiate" #-}
    do
        typeUFs <- {-# SCC "instantiate.freshtvs" #-}traverse freshMetaVar typeVars
        recordUFs <- {-# SCC "instantiate.freshrtvs" #-}traverse freshMetaVar recordVars
        sumUFs <- {-# SCC "instantiate.freshstvs" #-}traverse freshMetaVar sumVars
        let go :: IntMap (MetaTypeAST t) -> T t -> Infer s (MetaTypeAST t)
            go binders (TVar (TVarName i)) = return (binders IntMap.! i)
            go _ (T typeAST) =
                Type.ntraverse (go typeUFs) (go recordUFs) (go sumUFs) typeAST
                <&> MetaTypeAST
        {-# SCC "instantiate.go" #-}typ & case tagRefl :: ASTTagEquality tag of
            IsTypeT -> go typeUFs
            IsCompositeT IsRecordC -> go recordUFs
            IsCompositeT IsSumC -> go sumUFs

repr :: MetaVar tag -> Infer s (MetaVar tag, Final tag)
repr x =
    do
        zone <- askEnv <&> envZone
        let go ref =
                RefZone.readRef zone ref >>= \case
                LinkFinal final -> return (ref, final)
                Link innerRef ->
                    do
                        (preFinal, final) <- go innerRef
                        -- path compression:
                        -- Point to the pre-final link, so that the
                        -- Final isn't copied but shared.
                        RefZone.writeRef zone ref (Link preFinal)
                        return (preFinal, final)
        liftST $ go x

schemeBindersSingleton :: forall tag. IsTag tag => TVarName tag -> Constraints tag -> SchemeBinders
schemeBindersSingleton (TVarName tvName) cs =
    case tagRefl :: ASTTagEquality tag of
    IsTypeT -> mempty { schemeTypeBinders = binders }
    IsCompositeT IsRecordC -> mempty { schemeRecordBinders = binders }
    IsCompositeT IsSumC -> mempty { schemeSumBinders = binders }
    where
        binders = IntMap.singleton tvName cs

type DerefCache = (RefMap (T 'TypeT), RefMap (T RecordT), RefMap (T SumT))
type Deref s = RSST RefSet SchemeBinders DerefCache (Infer s)

derefCache :: forall tag. IsTag tag => RefZone.Ref (Link tag) -> Lens' DerefCache (Maybe (T tag))
derefCache tag =
    ( case (tagRefl :: ASTTagEquality tag) of
      IsTypeT                -> _1
      IsCompositeT IsRecordC -> _2
      IsCompositeT IsSumC    -> _3
    ) . RefMap.at tag
derefVar :: IsTag tag => MetaVar tag -> Deref s (T tag)
derefVar var =
    do
        (ref, final) <- lift (repr var)
        visited <- RSS.ask
        when (ref `RefSet.isMember` visited) $
            lift (throwError InfiniteType)
        cached <- Lens.use (derefCache ref)
        case cached of
            Just t -> pure t
            Nothing ->
                case final of
                Bound ast -> derefAST ast & RSS.local (RefSet.insert ref)
                Unbound cs ->
                    do
                        tvName <- nextFresh <&> TVarName & lift
                        schemeBindersSingleton tvName cs & RSS.tell
                        return $ TVar tvName
            >>= (derefCache ref <?=)

deref :: IsTag tag => MetaTypeAST tag -> Deref s (T tag)
deref = \case
    MetaTypeAST ast -> derefAST ast
    MetaTypeVar var -> derefVar var

derefAST :: IsTag tag => Type.AST tag MetaTypeAST -> Deref s (T tag)
derefAST = fmap T . Type.ntraverse deref deref deref

generalize :: MetaType -> Infer s (Scheme 'TypeT)
generalize t =
    {-# SCC "generalize" #-}
    runRSST (deref t) mempty mempty
    <&> (\(x, _, w) -> Scheme w x)
