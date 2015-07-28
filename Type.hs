{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TypeOperators #-}
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
module Type
    ( Infer, runInfer, inferScheme, infer
    , Err(..)
    , Scope, newScope, emptyScope

    , CompositeTag(..), RecordT
    , ASTTag(..)
    , Type, Record
    , TypeAST(..), bitraverse, typeSubexprs
    , SchemeBinders(..)
    , Scheme(..)

    , T(..), V(..), AV(..)

    , recordType, compositeFrom, (~>), tInst
    , intType, boolType
    , lam, lambda, lambdaRecord
    , recVal, global, litInt
    , ($$), ($=), ($.), ($+), ($-), ($$:)

    , forAll
    , test
    , example1, example2, example3, example4, example5, example6, example7, example8
    , runTests
    ) where

import           Prelude.Compat hiding (abs)

import           Control.DeepSeq (NFData(..))
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Lens.Tuple
import           Control.Monad (unless, void)
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
import           Data.String (IsString(..))
import           Data.Type.Equality
import qualified Data.UnionFind.ST as UF
import           GHC.Generics (Generic)
import           MapPretty ()
import           Text.PrettyPrint (isEmpty, fcat, hcat, punctuate, Doc, (<+>), (<>), text)
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)
import           WriterT

data CompositeTag = RecordC | SumC
type RecordT = 'CompositeT 'RecordC
type SumT = 'CompositeT 'SumC
data ASTTag = TypeT | CompositeT CompositeTag

data CompositeTagEquality c
    = IsRecordC (c :~: 'RecordC)
    | IsSumC (c :~: 'SumC)

data ASTTagEquality t where
    IsTypeT :: (t :~: 'TypeT) -> ASTTagEquality t
    IsCompositeT :: CompositeTagEquality c -> (t :~: 'CompositeT c) -> ASTTagEquality t

class IsCompositeTag t where
    compositeTagRefl :: CompositeTagEquality t
    compositeChar :: Proxy t -> Char
instance IsCompositeTag 'RecordC where
    compositeTagRefl = IsRecordC Refl
    compositeChar _ = '*'
instance IsCompositeTag 'SumC where
    compositeTagRefl = IsSumC Refl
    compositeChar _ = '+'

class IsTag t where tagRefl :: ASTTagEquality t
instance IsTag 'TypeT where tagRefl = IsTypeT Refl
instance IsCompositeTag c => IsTag ('CompositeT c) where
    tagRefl = IsCompositeT compositeTagRefl Refl

newtype TVarName (tag :: ASTTag) = TVarName { _tVarName :: Int }
    deriving (Eq, Ord, Show, Pretty, NFData)

data TypeAST tag ast where
    TFun :: !(ast 'TypeT) -> !(ast 'TypeT) -> TypeAST 'TypeT ast
    TInst :: String -> TypeAST 'TypeT ast
    TRecord :: !(ast RecordT) -> TypeAST 'TypeT ast
    TSum :: !(ast SumT) -> Type ast
    TEmptyComposite :: IsCompositeTag c => TypeAST ('CompositeT c) ast
    TCompositeExtend ::
        IsCompositeTag c => String -> !(ast 'TypeT) ->
        !(ast ('CompositeT c)) ->
        TypeAST ('CompositeT c) ast

type Type = TypeAST 'TypeT
type Record = TypeAST RecordT
type Composite c = TypeAST ('CompositeT c)

instance (NFData (ast 'TypeT), NFData (ast RecordT), NFData (ast SumT), NFData (ast tag)) =>
         NFData (TypeAST tag ast) where
    rnf (TFun x y) = rnf x `seq` rnf y
    rnf (TInst n) = rnf n
    rnf (TRecord record) = rnf record
    rnf (TSum s) = rnf s
    rnf TEmptyComposite = ()
    rnf (TCompositeExtend n t r) = rnf n `seq` rnf t `seq` rnf r

bitraverse ::
    Applicative f =>
    (ast 'TypeT -> f (ast' 'TypeT)) ->
    (ast RecordT -> f (ast' RecordT)) ->
    (ast SumT -> f (ast' SumT)) ->
    TypeAST tag ast -> f (TypeAST tag ast')
bitraverse typ reco su = \case
    TFun a b -> TFun <$> typ a <*> typ b
    TInst n -> pure (TInst n)
    TRecord r -> TRecord <$> reco r
    TSum s -> TSum <$> su s
    TEmptyComposite -> pure TEmptyComposite
    TCompositeExtend n t (r :: ast ('CompositeT c)) ->
        TCompositeExtend n <$> typ t <*>
        case compositeTagRefl :: CompositeTagEquality c of
        IsRecordC Refl -> reco r
        IsSumC Refl -> su r

typeSubexprs ::
    forall f t ast ast'. (Applicative f, IsTag t) =>
    (forall tag. IsTag tag => ast tag -> f (ast' tag)) ->
    TypeAST t ast -> f (TypeAST t ast')
typeSubexprs f = bitraverse f f f

_TFun :: Lens.Prism' (TypeAST 'TypeT ast) (ast 'TypeT, ast 'TypeT)
_TFun = Lens.prism' (uncurry TFun) $ \case
    TFun x y -> Just (x, y)
    _ -> Nothing

_TInst :: Lens.Prism' (Type a) String
_TInst = Lens.prism' TInst $ \case
    TInst n -> Just n
    _ -> Nothing

_TRecord :: Lens.Prism' (Type ast) (ast RecordT)
_TRecord = Lens.prism' TRecord $ \case
    TRecord n -> Just n
    _ -> Nothing

_TSum :: Lens.Prism' (Type ast) (ast SumT)
_TSum = Lens.prism' TSum $ \case
    TSum n -> Just n
    _ -> Nothing

_TEmptyComposite :: Lens.Prism' (Record a) ()
_TEmptyComposite = Lens.prism' (\() -> TEmptyComposite) $ \case
    TEmptyComposite -> Just ()
    _ -> Nothing

_TCompositeExtend :: Lens.Prism' (Record ast) (String, ast 'TypeT, ast RecordT)
_TCompositeExtend = Lens.prism' (\(n, t, r) -> TCompositeExtend n t r) $ \case
    TCompositeExtend n t r -> Just (n, t, r)
    _ -> Nothing

instance (Pretty (ast 'TypeT), Pretty (ast RecordT), Pretty (ast SumT)) => Pretty (Type ast) where
    pPrintPrec level prec ast =
        case ast of
        TFun a b ->
            maybeParens (prec > 0) $
            pPrintPrec level 1 a <+> "->" <+> pPrintPrec level 0 b
        TInst name -> "#" <> text name
        TRecord r -> pPrintPrec level prec r
        TSum s -> pPrintPrec level prec s

instance (IsCompositeTag c, Pretty (ast 'TypeT), Pretty (ast ('CompositeT c))) => Pretty (Composite c ast) where
    pPrintPrec level prec ast =
        case ast of
        TEmptyComposite -> "{}"
        TCompositeExtend n t r ->
            maybeParens (prec > 1) $
            "{" <+> text n <+> ":" <+> pPrintPrec level 0 t <+> "}" <+>
            text [compositeChar (Proxy :: Proxy c)] <+> pPrintPrec level 1 r


data Leaf
    = LVar String
    | LGlobal String
    | LEmptyRecord
    | LInt Int
    deriving (Show)

instance Pretty Leaf where
    pPrint (LVar x) = text x
    pPrint (LGlobal x) = text x
    pPrint LEmptyRecord = "{}"
    pPrint (LInt x) = pPrint x

data Abs v = Abs String !v
    deriving (Show, Functor, Foldable, Traversable)

data App v = App !v !v
    deriving (Show, Functor, Foldable, Traversable)

data RecExtend v = RecExtend String !v !v
    deriving (Show, Functor, Foldable, Traversable)

data GetField v = GetField !v String
    deriving (Show, Functor, Foldable, Traversable)

data Inject v = Inject String !v
    deriving (Show, Functor, Foldable, Traversable)

data Val v
    = BLam (Abs v)
    | BApp (App v)
    | BRecExtend (RecExtend v)
    | BGetField (GetField v)
    | BInject (Inject v)
    | BLeaf Leaf
    deriving (Show, Functor, Foldable, Traversable)

instance Pretty v => Pretty (Val v) where
    pPrintPrec level prec (BLam (Abs name body)) =
        maybeParens (prec > 0) $
        text name <+> "=>" <+> pPrintPrec level 0 body
    pPrintPrec level prec (BApp (App func arg)) =
        maybeParens (prec > 9) $
        pPrintPrec level 9 func <+> pPrintPrec level 10 arg
    pPrintPrec level prec (BRecExtend (RecExtend name val rest)) =
        maybeParens (prec > 7) $
        text name <> "="
        <> pPrintPrec level 8 val <+> "*"
        <+> pPrintPrec level 7 rest
    pPrintPrec level prec (BGetField (GetField val name)) =
        maybeParens (prec > 8) $
        pPrintPrec level 8 val <> "." <> text name
    pPrintPrec level prec (BInject (Inject name val)) =
        maybeParens (prec > 8) $
        text name <+> pPrintPrec level 8 val
    pPrintPrec level prec (BLeaf leaf) = pPrintPrec level prec leaf

newtype V = V (Val V)
    deriving (Show, Pretty)

data AV a = AV
    { aAnnotation :: a
    , aVal :: Val (AV a)
    } deriving (Show, Functor, Foldable, Traversable)
instance Pretty a => Pretty (AV a) where
    pPrintPrec level prec (AV ann v)
        | isEmpty annDoc = pPrintPrec level prec v
        | otherwise =
        "{" <> annDoc <> "}" <>
        pPrintPrec level 10 v
        where
            annDoc = pPrint ann

data T tag
    = T (TypeAST tag T)
    | TVar (TVarName tag)
    deriving (Generic)
instance NFData (T tag)

instance Pretty (TypeAST tag T) => Pretty (T tag) where
    pPrintPrec level prec (T typ) = pPrintPrec level prec typ
    pPrintPrec _ _ (TVar name) = text "a" <> pPrint name

infixr 4 ~>
(~>) :: T 'TypeT -> T 'TypeT -> T 'TypeT
a ~> b = T $ TFun a b

compositeFrom :: IsCompositeTag c => [(String, T 'TypeT)] -> T ('CompositeT c)
compositeFrom [] = T TEmptyComposite
compositeFrom ((name, typ):fs) = T $ TCompositeExtend name typ $ compositeFrom fs

recordType :: [(String, T 'TypeT)] -> T 'TypeT
recordType = T . TRecord . compositeFrom

tInst :: String -> T 'TypeT
tInst = T . TInst

intType :: T 'TypeT
intType = tInst "Int"

boolType :: T 'TypeT
boolType = T $ TInst "Bool"

lam :: String -> V -> V
lam name body = V $ BLam $ Abs name body

lambda :: String -> (V -> V) -> V
lambda name body = lam name $ body (fromString name)

lambdaRecord :: String -> [String] -> ([V] -> V) -> V
lambdaRecord name fields body = lambda name $ \v -> body $ map (v $.) fields

litInt :: Int -> V
litInt = V . BLeaf . LInt

infixl 4 $$
($$) :: V -> V -> V
($$) f a = V $ BApp $ App f a

($$:) :: V -> [(String, V)] -> V
func $$: fields = func $$ recVal fields

recVal :: [(String, V)] -> V
recVal = foldr extend empty
    where
        extend (name, val) rest = V $ BRecExtend (RecExtend name val rest)
        empty = V $ BLeaf LEmptyRecord

($=) :: String -> V -> V -> V
(x $= y) z = V $ BRecExtend $ RecExtend x y z

($.) :: V -> String -> V
x $. y = V $ BGetField $ GetField x y

(.$) :: String -> V -> V
x .$ y = V $ BInject $ Inject x y

global :: String -> V
global = V . BLeaf . LGlobal

infixType :: T 'TypeT -> T 'TypeT -> T 'TypeT -> T 'TypeT
infixType a b c = recordType [("l", a), ("r", b)] ~> c

infixApp :: String -> V -> V -> V
infixApp name x y = global name $$: [("l", x), ("r", y)]

($+) :: V -> V -> V
($+) = infixApp "+"

($-) :: V -> V -> V
($-) = infixApp "-"

instance IsString V where
    fromString = V . BLeaf . LVar

data Err
    = DoesNotUnify Doc Doc
    | VarNotInScope String
    | InfiniteType
    | DuplicateFields [String]
    deriving (Show)

intercalate :: Doc -> [Doc] -> Doc
intercalate sep = hcat . punctuate sep

instance Pretty Err where
    pPrint (DoesNotUnify expected got) =
        "expected:" <+> expected <+> "but got:" <+> got
    pPrint (VarNotInScope name) =
        text name <+> "not in scope!"
    pPrint InfiniteType =
        "Infinite type encountered"
    pPrint (DuplicateFields names) =
        "Duplicate fields in record:" <+>
        (intercalate ", " . map text) names

newtype Infer s a = Infer
    { unInfer :: STRef s Int -> ST s (Either Err a) }
    deriving (Functor)
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

runInfer :: (forall s. Infer s a) -> Either Err a
runInfer act = runST $ newSTRef 0 >>= unInfer act

{-# INLINE liftST #-}
liftST :: ST s a -> Infer s a
liftST act = Infer $ \_ -> act <&> Right

throwError :: Err -> Infer s a
throwError err = Infer $ \_ -> return $ Left err

modify' :: (Int -> Int) -> Infer s Int
modify' f =
    Infer $ \s ->
    do
        old <- readSTRef s
        let new = f old
        writeSTRef s $! new
        return (Right new)

data Constraints tag where
    TypeConstraints :: Constraints 'TypeT
    -- forbidden field set:
    CompositeConstraints :: !(Set String) -> Constraints ('CompositeT c)

instance NFData (Constraints tag) where
    rnf TypeConstraints = ()
    rnf (CompositeConstraints cs) = rnf cs

instance Monoid (Constraints 'TypeT) where
    mempty = TypeConstraints
    mappend _ _ = TypeConstraints

instance Monoid (Constraints ('CompositeT c)) where
    mempty = CompositeConstraints mempty
    mappend (CompositeConstraints x) (CompositeConstraints y) =
        CompositeConstraints (x `mappend` y)

data TypeASTPosition s tag = TypeASTPosition
    { __tastPosNames :: Set (TVarName tag)
    , _tastPosType :: Either (Constraints tag) (TypeAST tag (UFTypeAST s))
    }

type UFType s = UFTypeAST s 'TypeT
type UFComposite c s = UFTypeAST s ('CompositeT c)
newtype UFTypeAST s tag = TS { tsUF :: UF.Point s (TypeASTPosition s tag) }
instance Pretty (UFTypeAST s tag) where
    pPrint _ = ".."

Lens.makeLenses ''TypeASTPosition

type TVarBinders tag = Map (TVarName tag) (Constraints tag)

data SchemeBinders = SchemeBinders
    { schemeTypeBinders :: TVarBinders 'TypeT
    , schemeRecordBinders :: TVarBinders RecordT
    , schemeSumBinders :: TVarBinders SumT
    } deriving (Generic)
instance NFData SchemeBinders
instance Monoid SchemeBinders where
    mempty = SchemeBinders Map.empty Map.empty Map.empty
    mappend (SchemeBinders t0 r0 s0) (SchemeBinders t1 r1 s1) =
        SchemeBinders
        (Map.unionWith mappend t0 t1)
        (Map.unionWith mappend r0 r1)
        (Map.unionWith mappend s0 s1)

nullBinders :: SchemeBinders -> Bool
nullBinders (SchemeBinders a b c) = Map.null a && Map.null b && Map.null c

data Scheme tag = Scheme
    { schemeBinders :: SchemeBinders
    , schemeType :: T tag
    } deriving (Generic)
instance NFData (Scheme tag)

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
        (map pPrintTV (Map.toList tvs) ++
         map pPrintTV (Map.toList rtvs) ++
         map pPrintTV (Map.toList stvs))

instance Pretty (TypeAST tag T) => Pretty (Scheme tag) where
    pPrint (Scheme binders typ)
        | nullBinders binders = pPrint typ
        | otherwise = pPrint binders <> "." <+> pPrint typ

data Scope s = Scope
    { _scopeLocals :: Map String (UFType s)
    , _scopeGlobals :: Map String (Scheme 'TypeT)
    }

newScope :: Map String (Scheme 'TypeT) -> Scope s
newScope = Scope Map.empty

emptyScope :: Scope s
emptyScope = Scope Map.empty Map.empty

{-# INLINE lookupLocal #-}
lookupLocal :: String -> Scope s -> Maybe (UFType s)
lookupLocal str (Scope locals _) = Map.lookup str locals

{-# INLINE lookupGlobal #-}
lookupGlobal :: String -> Scope s -> Maybe (Scheme 'TypeT)
lookupGlobal str (Scope _ globals) = Map.lookup str globals

{-# INLINE insertLocal #-}
insertLocal :: String -> UFType s -> Scope s -> Scope s
insertLocal name typ (Scope locals globals) =
    Scope (Map.insert name typ locals) globals

{-# INLINE freshTVarName #-}
freshTVarName :: Infer s (TVarName tag)
freshTVarName = modify' (+1) <&> TVarName

{-# INLINE newPosition #-}
newPosition ::
    Either (Constraints tag) (TypeAST tag (UFTypeAST s)) ->
    Infer s (UFTypeAST s tag)
newPosition t =
    do
        tvarName <- freshTVarName
        TypeASTPosition (Set.singleton tvarName) t
            & liftST . UF.fresh <&> TS

{-# INLINE freshTVar #-}
freshTVar :: Constraints tag -> Infer s (UFTypeAST s tag)
freshTVar = newPosition . Left

{-# INLINE wrap #-}
wrap :: TypeAST tag (UFTypeAST s) -> Infer s (UFTypeAST s tag)
wrap = newPosition . Right

instantiate :: forall s tag. IsTag tag => Scheme tag -> Infer s (UFTypeAST s tag)
instantiate (Scheme (SchemeBinders typeVars recordVars sumVars) typ) =
    do
        typeUFs <- traverse freshTVar typeVars
        recordUFs <- traverse freshTVar recordVars
        sumUFs <- traverse freshTVar sumVars
        let lookupTVar :: forall t. IsTag t => TVarName t -> UFTypeAST s t
            lookupTVar tvar =
                case tagRefl :: ASTTagEquality t of
                IsTypeT Refl -> typeUFs Map.! tvar
                IsCompositeT (IsRecordC Refl) Refl -> recordUFs Map.! tvar
                IsCompositeT (IsSumC Refl) Refl -> sumUFs Map.! tvar
        let go :: forall t. IsTag t => T t -> Infer s (UFTypeAST s t)
            go (TVar tvarName) = return (lookupTVar tvarName)
            go (T typeAST) = typeSubexprs go typeAST >>= wrap
        go typ

getWrapper :: UFTypeAST s tag -> Infer s (TypeASTPosition s tag)
getWrapper (TS r) = UF.descriptor r & liftST

deref ::
    forall s tag. IsTag tag =>
    Set Int ->
    UFTypeAST s tag -> WriterT SchemeBinders (Infer s) (T tag)
deref visited ts =
    lift (getWrapper ts) >>= \(TypeASTPosition names typ) ->
    let tvName = Set.findMin names
    in if _tVarName tvName `Set.member` visited
    then throwError InfiniteType & lift
    else
    case typ of
    Left cs ->
        do
            tell $
                case tagRefl :: ASTTagEquality tag of
                IsTypeT Refl -> mempty { schemeTypeBinders = binders }
                IsCompositeT (IsRecordC Refl) Refl -> mempty { schemeRecordBinders = binders }
                IsCompositeT (IsSumC Refl) Refl -> mempty { schemeSumBinders = binders }
            return $ TVar tvName
        where
            binders = Map.singleton tvName cs
    Right t -> t & typeSubexprs (deref (Set.insert (_tVarName tvName) visited)) <&> T

generalize :: UFType s -> Infer s (Scheme 'TypeT)
generalize t =
    deref Set.empty t
    & runWriterT
    <&> uncurry (flip Scheme)

unifyMatch :: Pretty v => Doc -> v -> Lens.Getting (Monoid.First a) v a -> Infer s a
unifyMatch expected vTyp prism =
    case vTyp ^? prism of
    Nothing -> throwError $ DoesNotUnify expected (pPrint vTyp)
    Just vcontent -> return vcontent

unifyMatchEq :: (Pretty v, Pretty a, Eq a) => Doc -> v -> a -> Lens.Getting (Monoid.First a) v a -> Infer s ()
unifyMatchEq expected vTyp u prism =
    do
        v <- unifyMatch expected vTyp prism
        unless (u == v) $ throwError $ DoesNotUnify (pPrint u) (pPrint vTyp)

type CompositeTail c s = UFComposite c s
type CompositeFields s = Map String (UFType s)
type ClosedComposite s = CompositeFields s
type OpenComposite c s = (CompositeFields s, CompositeTail c s)

data FlatComposite c s = FlatComposite
    { __frMTail :: Maybe (CompositeTail c s)
    , _frFields :: CompositeFields s
    }

Lens.makeLenses ''FlatComposite

flattenVal :: Composite c (UFTypeAST s) -> Infer s (FlatComposite c s)
flattenVal TEmptyComposite = return $ FlatComposite Nothing Map.empty
flattenVal (TCompositeExtend n t r) =
    flatten r <&> frFields . Lens.at n ?~ t
    where
        flatten ts =
            getWrapper ts <&> _tastPosType >>= \case
            Left _ -> return $ FlatComposite (Just ts) Map.empty
            Right typ -> flattenVal typ

unflatten :: IsCompositeTag c => FlatComposite c s -> Infer s (UFComposite c s)
unflatten (FlatComposite mTail fields) =
    Map.toList fields & go
    where
        go [] =
            case mTail of
            Nothing -> wrap TEmptyComposite
            Just tailVal -> return tailVal
        go ((name, typ):fs) = go fs <&> TCompositeExtend name typ >>= wrap

unifyClosedComposites :: ClosedComposite s -> ClosedComposite s -> Infer s ()
unifyClosedComposites uFields vFields
    | Map.keysSet uFields == Map.keysSet vFields = return ()
    | otherwise =
          throwError $
          DoesNotUnify
          ("Record fields:" <+> pPrint (Map.keys uFields))
          ("Record fields:" <+> pPrint (Map.keys vFields))

unifyOpenComposite :: IsCompositeTag c => OpenComposite c s -> ClosedComposite s -> Infer s ()
unifyOpenComposite (uFields, uTail) vFields
    | Map.null uniqueUFields =
          do
              tailVal <- unflatten $ FlatComposite Nothing uniqueVFields
              unify (\_ _ -> return ()) uTail tailVal
    | otherwise =
          throwError $
          DoesNotUnify
          ("Record with at least fields:" <+> pPrint (Map.keys uFields))
          ("Record fields:" <+> pPrint (Map.keys vFields))

    where
        uniqueUFields = uFields `Map.difference` vFields
        uniqueVFields = vFields `Map.difference` uFields

unifyOpenComposites :: IsCompositeTag c => OpenComposite c s -> OpenComposite c s -> Infer s ()
unifyOpenComposites (uFields, uTail) (vFields, vTail) =
    do
        commonRest <-
            freshTVar $ CompositeConstraints $
            Map.keysSet uFields `Set.union`
            Map.keysSet vFields
        uRest <- FlatComposite (Just commonRest) uniqueVFields & unflatten
        vRest <- FlatComposite (Just commonRest) uniqueUFields & unflatten
        unifyComposite uTail uRest
        unifyComposite vTail vRest
    where
        uniqueUFields = uFields `Map.difference` vFields
        uniqueVFields = vFields `Map.difference` uFields

unifyComposite :: IsCompositeTag c => UFComposite c s -> UFComposite c s -> Infer s ()
unifyComposite =
    unify f
    where
        -- We already know we are record vals, and will re-read them
        -- via flatten, so no need for unify's read of these:
        f TEmptyComposite TEmptyComposite = return ()
        f (TCompositeExtend un ut ur) (TCompositeExtend vn vt vr)
            | un == vn =
            do
                unifyType ut vt
                unifyComposite ur vr
        f u v =
            do
                FlatComposite uMTail uFields <- flattenVal u
                FlatComposite vMTail vFields <- flattenVal v
                Map.intersectionWith unifyType uFields vFields
                    & sequenceA_
                case (uMTail, vMTail) of
                    (Nothing, Nothing) -> unifyClosedComposites uFields vFields
                    (Just uTail, Nothing) -> unifyOpenComposite (uFields, uTail) vFields
                    (Nothing, Just vTail) -> unifyOpenComposite (vFields, vTail) uFields
                    (Just uTail, Just vTail) -> unifyOpenComposites (uFields, uTail) (vFields, vTail)

constraintsCheck :: Constraints tag -> TypeAST tag (UFTypeAST s) -> Infer s ()
constraintsCheck TypeConstraints _ = return ()
constraintsCheck old@(CompositeConstraints names) r =
    do
        FlatComposite mTail fields <- flattenVal r
        let fieldsSet = Map.keysSet fields
        let forbidden = Set.intersection fieldsSet names
        unless (Set.null forbidden) $ throwError $ DuplicateFields $
            Set.toList forbidden
        case mTail of
            Nothing -> return ()
            Just rTail -> setConstraints rTail (old `mappend` CompositeConstraints fieldsSet)

setConstraints :: Monoid (Constraints tag) => UFTypeAST s tag -> Constraints tag -> Infer s ()
setConstraints u constraints =
    UF.modifyDescriptor (tsUF u) (tastPosType . Lens._Left <>~ constraints) & liftST & void


{-# INLINE union #-}
union :: UF.Point s a -> UF.Point s a -> (a -> a -> (a, b)) -> ST s (Maybe b)
union x y f =
    do
        ref <- newSTRef $ Nothing
        UF.union' x y $ \a b ->
            do
                let (desc, result) = f a b
                writeSTRef ref $ Just result
                return desc
        readSTRef ref

unify ::
    (IsTag tag, Monoid (Constraints tag)) =>
    (TypeAST tag (UFTypeAST s) ->
     TypeAST tag (UFTypeAST s) -> Infer s ()) ->
    UFTypeAST s tag -> UFTypeAST s tag -> Infer s ()
unify f u v =
    union (tsUF u) (tsUF v) g
    & liftST
    >>= maybe (return ()) id
    where
        g (TypeASTPosition uNames uMTyp) (TypeASTPosition vNames vMTyp) =
            case (uMTyp, vMTyp) of
            (Left uCs, Left vCs) -> (Left (uCs `mappend` vCs), return ())
            (Left uCs, Right y) -> (Right y, constraintsCheck uCs y)
            (Right x, Left vCs) -> (Right x, constraintsCheck vCs x)
            (Right x, Right y) -> (Right x, f x y)
            & _1 %~ TypeASTPosition (uNames `mappend` vNames)

unifyType :: UFType s -> UFType s -> Infer s ()
unifyType =
    unify f
    where
        f (TInst uName) vTyp =
            unifyMatchEq "TInst" vTyp uName _TInst
        f (TRecord uRec) vTyp =
            do
                vRec <- unifyMatch "TRecord" vTyp _TRecord
                unifyComposite uRec vRec
        f (TSum uSum) vTyp =
            do
                vSum <- unifyMatch "TSum" vTyp _TSum
                unifyComposite uSum vSum
        f (TFun uArg uRes) vTyp =
            do
                (vArg, vRes) <- unifyMatch "TFun" vTyp _TFun
                unifyType uArg vArg
                unifyType uRes vRes

inferLeaf :: Scope s -> Leaf -> Infer s (UFType s)
inferLeaf scope leaf =
    case leaf of
    LEmptyRecord -> wrap TEmptyComposite >>= wrap . TRecord
    LGlobal n ->
        case lookupGlobal n scope of
        Just scheme -> instantiate scheme
        Nothing -> throwError $ VarNotInScope n
    LInt _ -> wrap (TInst "Int")
    LVar n ->
        case lookupLocal n scope of
        Just typ -> return typ
        Nothing -> throwError $ VarNotInScope n

inferLam :: Scope s -> Abs V -> Infer s (UFType s)
inferLam scope (Abs n body) =
    do
        nType <- freshTVar TypeConstraints
        resType <- infer (insertLocal n nType scope) body
        TFun nType resType & wrap

inferApp :: Scope s -> App V -> Infer s (UFType s)
inferApp scope (App fun arg) =
    do
        funTyp <- infer scope fun
        argTyp <- infer scope arg
        resTyp <- freshTVar TypeConstraints

        expectedFunTyp <- TFun argTyp resTyp & wrap
        unifyType expectedFunTyp funTyp
        return resTyp

inferRecExtend :: Scope s -> RecExtend V -> Infer s (UFType s)
inferRecExtend scope (RecExtend name val rest) =
    do
        valTyp <- infer scope val
        restTyp <- infer scope rest
        unknownRestFields <- freshTVar $ CompositeConstraints $ Set.singleton name
        expectedResTyp <- TRecord unknownRestFields & wrap
        unifyType expectedResTyp restTyp
        TCompositeExtend name valTyp unknownRestFields
            & wrap
            >>= wrap . TRecord

inferGetField :: Scope s -> GetField V -> Infer s (UFType s)
inferGetField scope (GetField val name) =
    do
        resTyp <- freshTVar TypeConstraints
        valTyp <- infer scope val
        expectedValTyp <-
            freshTVar (CompositeConstraints (Set.singleton name))
            <&> TCompositeExtend name resTyp
            >>= wrap
            >>= wrap . TRecord
        unifyType expectedValTyp valTyp
        return resTyp

inferInject :: Scope s -> Inject V -> Infer s (UFType s)
inferInject scope (Inject name val) =
    do
        valTyp <- infer scope val
        freshTVar (CompositeConstraints (Set.singleton name))
            <&> TCompositeExtend name valTyp
            >>= wrap
            >>= wrap . TSum

infer :: Scope s -> V -> Infer s (UFType s)
infer scope (V v) =
    case v of
    BLeaf l -> inferLeaf scope l
    BLam abs -> inferLam scope abs
    BApp app -> inferApp scope app
    BRecExtend ext -> inferRecExtend scope ext
    BGetField ext -> inferGetField scope ext
    BInject ext -> inferInject scope ext

inferScheme :: (forall s. Scope s) -> V -> Either Err (Scheme 'TypeT)
inferScheme scope x = runInfer $ infer scope x >>= generalize

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

globals :: Map String (Scheme 'TypeT)
globals =
    mconcat
    [ "+" ==> intInfix
    , "-" ==> intInfix
    ]
    where
        intInfix = forAll 0 0 0 $ \ [] [] [] -> infixType intType intType intType
        (==>) = Map.singleton

(<+?>) :: Doc -> Doc -> Doc
x <+?> y = fcat [x, " ", y]

test :: V -> IO ()
test x =
    print $ pPrint x <+?>
    case inferScheme (newScope globals) x of
    Left err -> "causes type error:" <+> pPrint err
    Right typ -> " :: " <+> pPrint typ


example1 :: V
example1 = lam "x" $ lam "y" $ "x" $$ "y" $$ "y"

example2 :: V
example2 = lam "x" $ recVal [] & "x" $= "x" & "y" $= lam "x" "x"

example3 :: V
example3 = lam "x" $ ("x" $. "y") $$ (lam "a" "a")

example4 :: V
example4 = lam "x" $ "x" $$ "x"

example5 :: V
example5 = lam "x" $ ("x" $. "y") $$ ("x" $. "y")

example6 :: V
example6 = recVal [("x", recVal []), ("y", recVal [])]

example7 :: V
example7 =
    lambdaRecord "params" ["x", "y", "z"] $ \[x, y, z] -> x $+ y $- z

example8 :: V
example8 =
    lambda "g" $ \g ->
    lambda "f" $ \f ->
    lambda "x" $ \x ->
    g $$ (f $$ "Just" .$ x)
      $$ (f $$ "Nothing" .$ recVal [])

runTests :: IO ()
runTests =
    mapM_ test
    [ example1
    , example2
    , example3
    , example4
    , example5
    , example6
    , example7
    , example8
    ]
