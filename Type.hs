{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Type
    ( Infer, runInfer, inferScheme, infer
    , Err(..)
    , Scope, newScope, emptyScope

    , Identifier(..)
    , TId(..), TParamId(..)
    , Type
    , TypeAST(..), ntraverse
    , SchemeBinders(..)
    , Scheme(..), forAll

    , T(..), TVarName(..)

    , recordType, compositeFrom, (~>), tInst
    , intType, boolType
    ) where

import           Control.DeepSeq (NFData(..))
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Lens.Tuple
import           Control.Monad (unless, zipWithM_)
import           Control.Monad.ST (ST, runST)
import           Control.Monad.Trans.Class (lift)
import           Data.Foldable (sequenceA_)
import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Monoid as Monoid
import           Data.Proxy (Proxy(..))
import           Data.STRef
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.String (IsString)
import           GHC.Exts (inline)
import           Identifier (Identifier(..), Tag(..))
import           MapPretty ()
import           PrettyUtils ((<+?>))
import qualified RefZone
import           RefZone (Zone)
import           Text.PrettyPrint (hcat, punctuate, Doc, (<+>), (<>), text)
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)
import           Type.Constraints (Constraints(..))
import           Type.Tag
    ( ASTTag(..), IsTag(..), ASTTagEquality(..)
    , IsCompositeTag(..), CompositeTagEquality(..)
    , RecordT, SumT )
import qualified Val
import           Val (Val(..))
import           Val.Annotated (AV(..))
import           Val.Pure (V(..))
import           WriterT

import           Prelude.Compat hiding (abs, tail)

newtype TVarName (tag :: ASTTag) = TVarName { _tVarName :: Int }
    deriving (Eq, Ord, Show, Pretty, NFData)

newtype TId = TId { _tid :: Identifier }
    deriving (Eq, Ord, Show, NFData, IsString, Pretty)

newtype TParamId = TParamId { _tParamId :: Identifier }
    deriving (Eq, Ord, Show, NFData, IsString, Pretty)

data TypeAST tag ast where
    TFun :: !(ast 'TypeT) -> !(ast 'TypeT) -> TypeAST 'TypeT ast
    TInst :: {-# UNPACK #-}!TId -> !(Map TParamId (ast 'TypeT)) -> TypeAST 'TypeT ast
    TRecord :: !(ast RecordT) -> TypeAST 'TypeT ast
    TSum :: !(ast SumT) -> TypeAST 'TypeT ast
    TEmptyComposite :: IsCompositeTag c => TypeAST ('CompositeT c) ast
    TCompositeExtend ::
        IsCompositeTag c => {-# UNPACK #-}!Tag -> !(ast 'TypeT) ->
        !(ast ('CompositeT c)) -> TypeAST ('CompositeT c) ast

type Type = TypeAST 'TypeT
type Composite c = TypeAST ('CompositeT c)

instance (NFData (ast 'TypeT),
          NFData (ast RecordT),
          NFData (ast SumT),
          NFData (ast tag)) =>
         NFData (TypeAST tag ast) where
    rnf (TFun x y) = rnf x `seq` rnf y
    rnf (TInst n params) = rnf n `seq` rnf params
    rnf (TRecord record) = rnf record
    rnf (TSum s) = rnf s
    rnf TEmptyComposite = ()
    rnf (TCompositeExtend n t r) = rnf n `seq` rnf t `seq` rnf r

{-# INLINE ntraverse #-}
ntraverse ::
    Applicative f =>
    (ast 'TypeT -> f (ast' 'TypeT)) ->
    (ast RecordT -> f (ast' RecordT)) ->
    (ast SumT -> f (ast' SumT)) ->
    TypeAST tag ast -> f (TypeAST tag ast')
ntraverse onTypes onRecords onSums = \case
    TFun a b -> TFun <$> onTypes a <*> onTypes b
    TInst n params -> TInst n <$> traverse onTypes params
    TRecord r -> TRecord <$> onRecords r
    TSum s -> TSum <$> onSums s
    TEmptyComposite -> pure TEmptyComposite
    TCompositeExtend n t (r :: ast ('CompositeT c)) ->
        TCompositeExtend n <$> onTypes t <*>
        case compositeTagRefl :: CompositeTagEquality c of
        IsRecordC -> onRecords r
        IsSumC -> onSums r

_TFun :: Lens.Prism' (TypeAST 'TypeT ast) (ast 'TypeT, ast 'TypeT)
_TFun = Lens.prism' (uncurry TFun) $ \case
    TFun x y -> Just (x, y)
    _ -> Nothing

_TInst :: Lens.Prism' (Type ast) (TId, Map TParamId (ast 'TypeT))
_TInst = Lens.prism' (uncurry TInst) $ \case
    TInst n p -> Just (n, p)
    _ -> Nothing

_TRecord :: Lens.Prism' (Type ast) (ast RecordT)
_TRecord = Lens.prism' TRecord $ \case
    TRecord n -> Just n
    _ -> Nothing

_TSum :: Lens.Prism' (Type ast) (ast SumT)
_TSum = Lens.prism' TSum $ \case
    TSum n -> Just n
    _ -> Nothing

_TEmptyComposite :: IsCompositeTag c => Lens.Prism' (TypeAST ('CompositeT c) ast) ()
_TEmptyComposite = Lens.prism' (\() -> TEmptyComposite) $ \case
    TEmptyComposite -> Just ()
    _ -> Nothing

_TCompositeExtend ::
    IsCompositeTag c =>
    Lens.Prism' (TypeAST ('CompositeT c) ast)
    (Tag, ast 'TypeT, ast ('CompositeT c))
_TCompositeExtend = Lens.prism' (\(n, t, r) -> TCompositeExtend n t r) $ \case
    TCompositeExtend n t r -> Just (n, t, r)
    _ -> Nothing

instance (Pretty (ast 'TypeT),
          Pretty (ast RecordT),
          Pretty (ast SumT)) =>
         Pretty (Type ast) where
    pPrintPrec level prec ast =
        case ast of
        TFun a b ->
            maybeParens (prec > 0) $
            pPrintPrec level 1 a <+> "->" <+?> pPrintPrec level 0 b
        TInst name params
            | Map.null params -> pPrint name
            | otherwise -> pPrint name <+> pPrint params
        TRecord r -> pPrintPrec level prec r
        TSum s -> pPrintPrec level prec s

instance (IsCompositeTag c,
          Pretty (ast 'TypeT),
          Pretty (ast ('CompositeT c))) =>
         Pretty (Composite c ast) where
    pPrintPrec level prec ast =
        case ast of
        TEmptyComposite -> "{}"
        TCompositeExtend n t r ->
            maybeParens (prec > 1) $
            "{" <+> pPrint n <+> ":" <+> pPrintPrec level 0 t <+> "}" <+?>
            text [compositeChar (Proxy :: Proxy c)] <+> pPrintPrec level 1 r

data T tag
    = T (TypeAST tag T)
    -- HACK: When skolems are properly supported, they'll be qualified
    -- vars inside the TypeAST itself
    | TVar (TVarName tag)
instance NFData (T tag) where
    rnf (T x) = rnf x
    rnf (TVar x) = rnf x

instance Pretty (TypeAST tag T) => Pretty (T tag) where
    pPrintPrec level prec (T typ) = pPrintPrec level prec typ
    pPrintPrec _ _ (TVar name) = text "a" <> pPrint name

infixr 4 ~>
(~>) :: T 'TypeT -> T 'TypeT -> T 'TypeT
a ~> b = T $ TFun a b

compositeFrom :: IsCompositeTag c => [(Tag, T 'TypeT)] -> T ('CompositeT c)
compositeFrom [] = T TEmptyComposite
compositeFrom ((name, typ):fs) = T $ TCompositeExtend name typ $ compositeFrom fs

recordType :: [(Tag, T 'TypeT)] -> T 'TypeT
recordType = T . TRecord . compositeFrom

tInst :: TId -> Map TParamId (T 'TypeT) -> T 'TypeT
tInst name params = T $ TInst name params

intType :: T 'TypeT
intType = tInst "Int" Map.empty

boolType :: T 'TypeT
boolType = tInst "Bool" Map.empty

int :: Type ast
int = TInst "Int" Map.empty

data IsBound tag bound
    = Unbound (Constraints tag)
    | Bound bound
    deriving (Functor, Foldable, Traversable)

data MetaVar tag = MetaVar
    { __unificationPosNames :: Set (TVarName tag)
      -- TODO: Remove names, use mutable bit/level instead
    , __unificationPosRef :: RefZone.Ref (IsBound tag (MetaTypeAST tag))
    }
instance NFData (MetaVar tag) where rnf (MetaVar x y) = rnf x `seq` rnf y
instance Pretty (MetaVar tag) where
    pPrint (MetaVar names _) = "?" <> pPrint (Set.toList names)

type MetaType = MetaTypeAST 'TypeT
type MetaComposite c = MetaTypeAST ('CompositeT c)
data MetaTypeAST tag
    = MetaTypeVar (MetaVar tag)
    | MetaTypeAST (TypeAST tag MetaTypeAST)
instance NFData (MetaTypeAST tag) where
    rnf (MetaTypeVar x) = rnf x
    rnf (MetaTypeAST x) = rnf x
instance Pretty (TypeAST tag MetaTypeAST) => Pretty (MetaTypeAST tag) where
    pPrint (MetaTypeVar pos) = pPrint pos
    pPrint (MetaTypeAST t) = pPrint t

Lens.makePrisms ''IsBound
Lens.makeLenses ''MetaVar

type TVarBinders tag = Map (TVarName tag) (Constraints tag)

data SchemeBinders = SchemeBinders
    { schemeTypeBinders :: TVarBinders 'TypeT
    , schemeRecordBinders :: TVarBinders RecordT
    , schemeSumBinders :: TVarBinders SumT
    }
instance NFData SchemeBinders where
    rnf (SchemeBinders x y z) = rnf x `seq` rnf y `seq` rnf z
instance Monoid SchemeBinders where
    mempty = SchemeBinders Map.empty Map.empty Map.empty
    mappend (SchemeBinders t0 r0 s0) (SchemeBinders t1 r1 s1)
        | enableAssertions =
            SchemeBinders
            -- TODO: Can use assert-same-constraints and compile out for
            -- perf instead of mappend
            (Map.unionWith assertSameConstraints t0 t1)
            (Map.unionWith assertSameConstraints r0 r1)
            (Map.unionWith assertSameConstraints s0 s1)
        | otherwise =
            SchemeBinders
            (Map.union t0 t1)
            (Map.union r0 r1)
            (Map.union s0 s1)
        where
            enableAssertions = False
            assertSameConstraints x y
                | x == y = x
                | otherwise =
                  "Differing constraints of same " ++
                  "unification variable encountered"
                  & error

nullBinders :: SchemeBinders -> Bool
nullBinders (SchemeBinders a b c) = Map.null a && Map.null b && Map.null c

data Scheme tag = Scheme
    { schemeBinders :: SchemeBinders
    , schemeType :: T tag
    }
instance NFData (Scheme tag) where
    rnf (Scheme x y) = rnf x `seq` rnf y

pPrintTV :: (TVarName tag, Constraints tag) -> Doc
pPrintTV (tv, constraints) =
    "∀a" <> pPrint tv <> suffix constraints
    where
        suffix :: Constraints tag -> Doc
        suffix TypeConstraints = ""
        suffix (CompositeConstraints cs) =
            "∉" <> (intercalate " " . map pPrint) (Set.toList cs)

instance Pretty SchemeBinders where
    pPrint (SchemeBinders tvs rtvs stvs) =
        intercalate " " $
        map pPrintTV (Map.toList tvs) ++
        map pPrintTV (Map.toList rtvs) ++
        map pPrintTV (Map.toList stvs)

instance Pretty (TypeAST tag T) => Pretty (Scheme tag) where
    pPrint (Scheme binders typ)
        | nullBinders binders = pPrint typ
        | otherwise = pPrint binders <> "." <+?> pPrint typ

forAll ::
    Int -> Int -> Int ->
    ([T 'TypeT] -> [T RecordT] -> [T SumT] -> T tag) ->
    Scheme tag
forAll nTvs nRtvs nStvs mkType =
    Scheme (SchemeBinders cTvs cRtvs cStvs) $
    mkType (map TVar tvs) (map TVar rtvs) (map TVar stvs)
    where
        cTvs = Map.fromList [ (tv, mempty) | tv <- tvs ]
        cRtvs = Map.fromList [ (tv, mempty) | tv <- rtvs ]
        cStvs = Map.fromList [ (tv, mempty) | tv <- stvs ]
        tvs = map TVarName [1..nTvs]
        rtvs = map TVarName [nTvs+1..nTvs+nRtvs]
        stvs = map TVarName [nTvs+nRtvs+1..nTvs+nRtvs+nStvs]

data Scope = Scope
    { _scopeLocals :: Map Val.Var MetaType
    , _scopeGlobals :: Map Val.GlobalId (Scheme 'TypeT)
    }

newScope :: Map Val.GlobalId (Scheme 'TypeT) -> Scope
newScope = Scope Map.empty

emptyScope :: Scope
emptyScope = Scope Map.empty Map.empty

{-# INLINE insertLocal #-}
insertLocal :: Val.Var -> MetaType -> Scope -> Scope
insertLocal name typ (Scope locals globals) =
    Scope (Map.insert name typ locals) globals

data Err
    = DoesNotUnify Doc Doc
    | VarNotInScope Val.Var
    | GlobalNotInScope Val.GlobalId
    | InfiniteType
    | DuplicateFields [Tag]
    deriving (Show)

intercalate :: Doc -> [Doc] -> Doc
intercalate sep = hcat . punctuate sep

instance Pretty Err where
    pPrint (DoesNotUnify expected got) =
        "expected:" <+> expected <+> "but got:" <+> got
    pPrint (VarNotInScope name) =
        pPrint name <+> "not in scope!"
    pPrint (GlobalNotInScope name) =
        pPrint name <+> "not in scope!"
    pPrint InfiniteType =
        "Infinite type encountered"
    pPrint (DuplicateFields names) =
        "Duplicate fields in record:" <+>
        (intercalate ", " . map pPrint) names

data Env s = Env
    { envFresh :: STRef s Int
    , envZone :: Zone s
    , envScope :: Scope
    }

newtype Infer s a = Infer
    { unInfer :: Env s -> ST s (Either Err a) }
    deriving (Functor)
-- TODO: Since Infer is completely equivalent to a single ReaderT
-- transform, it is likely that ReaderT will be no slower, bench it
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

runInfer :: Scope -> (forall s. Infer s a) -> Either Err a
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
localScope :: (Scope -> Scope) -> Infer s a -> Infer s a
localScope f = localEnv $ \e -> e { envScope = f (envScope e) }

{-# INLINE askScope #-}
askScope :: Infer s Scope
askScope = askEnv <&> envScope

{-# INLINE lookupLocal #-}
lookupLocal :: Val.Var -> Infer s (Maybe MetaType)
lookupLocal str = askScope <&> _scopeLocals <&> Map.lookup str

{-# INLINE lookupGlobal #-}
lookupGlobal :: Val.GlobalId -> Infer s (Maybe (Scheme 'TypeT))
lookupGlobal str = askScope <&> _scopeGlobals <&> Map.lookup str

nextFresh :: Infer s Int
nextFresh =
    askEnv <&> envFresh >>= \ref ->
    do
        old <- readSTRef ref
        let !new = 1 + old
        writeSTRef ref $! new
        return new
    & liftST

{-# INLINE freshTVarName #-}
freshTVarName :: Infer s (TVarName tag)
freshTVarName = nextFresh <&> TVarName

freshPos :: Constraints tag -> Infer s (MetaVar tag)
freshPos cs =
    do
        tvarName <- freshTVarName
        ref <- Unbound cs & newRef
        MetaVar (Set.singleton tvarName) ref & return

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
        let go ::
                Map (TVarName t) (MetaTypeAST t) ->
                T t -> Infer s (MetaTypeAST t)
            go binders (TVar tvarName) = return (binders Map.! tvarName)
            go _ (T typeAST) =
                ntraverse (go typeUFs) (go recordUFs) (go sumUFs) typeAST
                <&> MetaTypeAST
        {-# SCC "instantiate.go" #-}typ & case tagRefl :: ASTTagEquality tag of
            IsTypeT -> go typeUFs
            IsCompositeT IsRecordC -> go recordUFs
            IsCompositeT IsSumC -> go sumUFs

repr ::
    MetaVar tag ->
    Infer s (MetaVar tag, IsBound tag (TypeAST tag MetaTypeAST))
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
schemeBindersSingleton tvName cs =
    case tagRefl :: ASTTagEquality tag of
    IsTypeT -> mempty { schemeTypeBinders = binders }
    IsCompositeT IsRecordC -> mempty { schemeRecordBinders = binders }
    IsCompositeT IsSumC -> mempty { schemeSumBinders = binders }
    where
        binders = Map.singleton tvName cs

deref ::
    forall s tag. IsTag tag =>
    Set Int -> MetaTypeAST tag -> WriterT SchemeBinders (Infer s) (T tag)
deref visited = \case
    MetaTypeAST ast ->
        ast & ntraverse (deref visited) (deref visited) (deref visited) <&> T
    MetaTypeVar (MetaVar names tvRef)
        | _tVarName tvName `Set.member` visited ->
              throwError InfiniteType & lift
        | otherwise ->
            -- TODO: Avoid Infer s monad and use ST directly?
            lift (readRef tvRef) >>= \case
            Unbound cs ->
                do
                    tell $ schemeBindersSingleton tvName cs
                    return $ TVar tvName
            Bound meta ->
                deref (Set.insert (_tVarName tvName) visited) meta
        where
            tvName = Set.findMin names

generalize :: MetaType -> Infer s (Scheme 'TypeT)
generalize t =
    {-# SCC "generalize" #-}
    deref Set.empty t
    & runWriterT
    <&> uncurry (flip Scheme)

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

flattenVal :: Composite c MetaTypeAST -> Infer s (FlatComposite c)
flattenVal TEmptyComposite =
    return $ FlatComposite Map.empty CompositeTailClosed
flattenVal (TCompositeExtend n t r) =
    flatten r <&> fcFields . Lens.at n ?~ t

flatten :: MetaComposite c -> Infer s (FlatComposite c)
flatten (MetaTypeAST ast) = flattenVal ast
flatten (MetaTypeVar pos) =
    repr pos >>= \case
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
unifyCompositesClosedClosed :: CompositeFields -> CompositeFields -> Infer s ()
unifyCompositesClosedClosed uFields vFields
    | Map.keysSet uFields == Map.keysSet vFields = return ()
    | otherwise =
          throwError $
          DoesNotUnify
          ("Record fields:" <+> prettyFieldNames uFields)
          ("Record fields:" <+> prettyFieldNames vFields)

flatConstraintsCheck :: Constraints ('CompositeT c) -> FlatComposite c -> Infer s ()
flatConstraintsCheck outerConstraints@(CompositeConstraints outerDisallowed) flatComposite =
    do
        let duplicates = Set.intersection (Map.keysSet innerFields) outerDisallowed
        unless (Set.null duplicates) $ throwError $ DuplicateFields $
            Set.toList duplicates
        case innerTail of
            CompositeTailClosed -> return ()
            CompositeTailOpen (MetaVar _ ref) innerConstraints ->
                writeRef ref $ Unbound $ outerConstraints `mappend` innerConstraints
    where
        FlatComposite innerFields innerTail = flatComposite

constraintsCheck ::
    Constraints tag -> TypeAST tag MetaTypeAST -> Infer s ()
constraintsCheck TypeConstraints _ = return ()
constraintsCheck cs@CompositeConstraints{} inner =
    ({-# SCC "constraintsCheck.flatten" #-}flattenVal inner) >>= flatConstraintsCheck cs

writeCompositeTail ::
    IsCompositeTag c =>
    (MetaVar ('CompositeT c), Constraints ('CompositeT c)) ->
    FlatComposite c -> Infer s ()
writeCompositeTail (pos, cs) composite =
    do
        {-# SCC "flatConstraintsCheck" #-}flatConstraintsCheck cs composite
        writePos pos $ Bound $ unflatten composite

{-# INLINE unifyCompositesOpenClosed #-}
unifyCompositesOpenClosed ::
    IsCompositeTag c =>
    (MetaVar ('CompositeT c), Constraints ('CompositeT c), CompositeFields) ->
    CompositeFields -> Infer s ()
unifyCompositesOpenClosed (openTailPos, openConstraints, openFields) closedFields
    | Map.null uniqueOpenFields =
          writeCompositeTail (openTailPos, openConstraints) $
          FlatComposite uniqueClosedFields CompositeTailClosed
    | otherwise =
          throwError $
          DoesNotUnify
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
    Infer s ()
unifyCompositesOpenOpen (uPos, uCs, uFields) (vPos, vCs, vFields) =
    do
        commonRest <- freshPos cs <&> (`CompositeTailOpen` cs)
        writeCompositeTail (uPos, uCs) $ FlatComposite uniqueVFields commonRest
        writeCompositeTail (vPos, vCs) $ FlatComposite uniqueUFields commonRest
    where
        cs = uCs `mappend` vCs
        uniqueUFields = uFields `Map.difference` vFields
        uniqueVFields = vFields `Map.difference` uFields

unifyComposite ::
    IsCompositeTag c => MetaComposite c -> MetaComposite c ->
    Infer s ()
unifyComposite = {-# SCC "unifyComposite" #-}unify unifyCompositeAST

-- We already know we are record vals, and will re-read them
-- via flatten, so no need for unify's read of these:
unifyCompositeAST ::
    IsCompositeTag c =>
    Composite c MetaTypeAST ->
    Composite c MetaTypeAST ->
    Infer s ()
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
    (IsTag tag, Monoid (Constraints tag)) =>
    (TypeAST tag MetaTypeAST ->
     TypeAST tag MetaTypeAST -> Infer s ()) ->
    MetaTypeAST tag -> MetaTypeAST tag -> Infer s ()
unify f (MetaTypeAST u) (MetaTypeAST v) = f u v
unify f (MetaTypeAST u) (MetaTypeVar v) = unifyVarAST f u v
unify f (MetaTypeVar u) (MetaTypeAST v) = unifyVarAST f v u
unify f (MetaTypeVar u) (MetaTypeVar v) =
    do
        (uPos@(MetaVar _ uRef), ur) <- repr u
        (vPos@(MetaVar _ vRef), vr) <- repr v
        -- TODO: Choose which to link into which weight/level-wise
        let link a b =
                -- TODO: Update the "names"? They should die!
                writePos a $ Bound $ MetaTypeVar b
        unless (uRef == vRef) $
            case (ur, vr) of
            (Unbound uCs, Unbound vCs) ->
                do
                    link uPos vPos
                    writeRef vRef $ Unbound $ uCs `mappend` vCs
            (Unbound uCs, Bound vAst) -> unifyUnbound uPos uCs vAst
            (Bound uAst, Unbound vCs) -> unifyUnbound vPos vCs uAst
            (Bound uAst, Bound vAst) ->
                do
                    link uPos vPos
                    f uAst vAst

unifyUnbound ::
    MetaVar tag -> Constraints tag -> TypeAST tag MetaTypeAST ->
    Infer s ()
unifyUnbound pos cs ast =
    do
        {-# SCC "constraintsCheck" #-}constraintsCheck cs ast
        writePos pos $ Bound (MetaTypeAST ast)

unifyVarAST ::
    (IsTag tag, Monoid (Constraints tag)) =>
    (TypeAST tag MetaTypeAST ->
     TypeAST tag MetaTypeAST -> Infer s ()) ->
    TypeAST tag MetaTypeAST -> MetaVar tag -> Infer s ()
unifyVarAST f uAst v =
    repr v >>= \case
    (_, Bound vAst) -> f uAst vAst
    (vPos, Unbound vCs) -> unifyUnbound vPos vCs uAst

unifyTInstParams ::
    Err -> Map TParamId MetaType -> Map TParamId MetaType -> Infer s ()
unifyTInstParams err uParams vParams
    | uSize /= vSize = throwError err
    | uSize == 0 = return ()
    | otherwise =
        zipWithM_ unifyParam (Map.toAscList uParams) (Map.toAscList vParams)
    where
        uSize = Map.size uParams
        vSize = Map.size vParams
        unifyParam (_, uParam) (_, vParam) = unifyType uParam vParam

unifyMatch :: Pretty v => Doc -> v -> Lens.Getting (Monoid.First a) v a -> Infer s a
unifyMatch expected vTyp prism =
    case vTyp ^? prism of
    Nothing -> throwError $ DoesNotUnify expected (pPrint vTyp)
    Just vcontent -> return vcontent

unifyType :: MetaType -> MetaType -> Infer s ()
unifyType = {-# SCC "unifyType" #-}unify unifyTypeAST

unifyTypeAST :: Type MetaTypeAST -> Type MetaTypeAST -> Infer s ()
unifyTypeAST uTyp@(TInst uName uParams) vTyp =
    case vTyp of
    TInst vName vParams | uName == vName ->
        {-# SCC "unifyTInstParams" #-}
        unifyTInstParams err uParams vParams
    _ -> throwError err
    where
        err = DoesNotUnify (pPrint uTyp) (pPrint vTyp)
unifyTypeAST (TRecord uRec) vTyp =
    do
        vRec <- unifyMatch "TRecord" vTyp _TRecord
        unifyComposite uRec vRec
unifyTypeAST (TSum uSum) vTyp =
    do
        vSum <- unifyMatch "TSum" vTyp _TSum
        unifyComposite uSum vSum
unifyTypeAST (TFun uArg uRes) vTyp =
    do
        (vArg, vRes) <- unifyMatch "TFun" vTyp _TFun
        unifyType uArg vArg
        unifyType uRes vRes

type InferResult = (AV MetaType, MetaType)

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
            res <- freshTVar TypeConstraints
            let emptySum = MetaTypeAST TEmptyComposite & TSum & MetaTypeAST
            TFun emptySum res & MetaTypeAST & return
    Val.LGlobal n ->
        {-# SCC "inferGlobal" #-}
        lookupGlobal n >>= \case
        Just scheme -> instantiate scheme
        Nothing -> throwError $ GlobalNotInScope n
    Val.LInt _ ->
        {-# SCC "inferInt" #-}
        MetaTypeAST int & return
    Val.LHole ->
        {-# SCC "inferHole" #-}
        freshTVar TypeConstraints
    Val.LVar n ->
        {-# SCC "inferVar" #-}
        lookupLocal n >>= \case
        Just typ -> return typ
        Nothing -> throwError $ VarNotInScope n
    <&> inferRes (Val.BLeaf leaf)

inferLam :: Val.Abs V -> Infer s InferResult
inferLam (Val.Abs n body) =
    {-# SCC "inferLam" #-}
    do
        nType <- freshTVar TypeConstraints
        (body', resType) <- infer body & localScope (insertLocal n nType)
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
                    resTyp <- freshTVar TypeConstraints
                    unifyVarAST unifyTypeAST (TFun argTyp resTyp) pos
                    return resTyp
            MetaTypeAST (TFun paramTyp resTyp) ->
                do
                    unifyType paramTyp argTyp
                    return resTyp
            MetaTypeAST t ->
                DoesNotUnify (pPrint t) "Function type" & throwError
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
                        freshTVar $ CompositeConstraints $
                        Set.singleton name
                    -- TODO (Optimization): pos known to be unbound
                    unifyVarAST unifyTypeAST (TRecord unknownRestFields) pos
                    return unknownRestFields
            MetaTypeAST (TRecord restRecordTyp) ->
                do
                    propagateConstraint restRecordTyp
                    return restRecordTyp
            MetaTypeAST t ->
                DoesNotUnify (pPrint t) "Record type" & throwError
        (val', valTyp) <- infer val
        TCompositeExtend name valTyp restRecordTyp
            & MetaTypeAST
            & TRecord & MetaTypeAST
            & inferRes (Val.BRecExtend (Val.RecExtend name val' rest'))
            & return
    where
        propagateConstraint (MetaTypeAST x) = propagateConstraintBound x
        propagateConstraint (MetaTypeVar pos) =
            repr pos >>= \case
            (_, Bound ast) -> propagateConstraintBound ast
            (vPos, Unbound (CompositeConstraints cs)) ->
                writePos vPos $ Unbound $ CompositeConstraints $
                Set.insert name cs
        propagateConstraintBound TEmptyComposite = return ()
        propagateConstraintBound (TCompositeExtend fieldTag _ restTyp)
            | fieldTag == name = DuplicateFields [name] & throwError
            | otherwise = propagateConstraint restTyp

inferCase :: Val.Case V -> Infer s InferResult
inferCase (Val.Case name handler restHandler) =
    {-# SCC "inferCase" #-}
    do
        resType <- freshTVar TypeConstraints
        let toResType x = TFun x resType & MetaTypeAST

        fieldType <- freshTVar TypeConstraints

        (handler', handlerTyp) <- infer handler
        (restHandler', restHandlerTyp) <- infer restHandler

        sumTail <- freshTVar $ CompositeConstraints $ Set.singleton name

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
        resTyp <- freshTVar TypeConstraints
        (val', valTyp) <- infer val
        expectedValTyp <-
            freshTVar (CompositeConstraints (Set.singleton name))
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
        freshTVar (CompositeConstraints (Set.singleton name))
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

inferScheme :: Scope -> V -> Either Err (AV MetaType, Scheme 'TypeT)
inferScheme scope x =
    {-# SCC "inferScheme" #-}
    runInfer scope $ infer x >>= inline _2 generalize
