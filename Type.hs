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
    , GlobalId(..), Var(..)
    , Tag(..)
    , CompositeTag(..), RecordT
    , ASTTag(..)
    , Type
    , TypeAST(..), ntraverse, typeSubexprs
    , SchemeBinders(..)
    , Scheme(..)

    , T(..), V(..), AV(..)

    , recordType, compositeFrom, (~>), tInst
    , intType, boolType
    , lam, lambda, lambdaRecord
    , absurd, case_, cases
    , recVal, global, var, litInt
    , hole
    , ($$), ($=), ($.), ($+), ($-), ($$:)

    , forAll
    , test
    , example1, example2, example3, example4, example5, example6, example7, example8, example9, example10, example11
    , runTests
    ) where

import           Prelude.Compat hiding (abs, tail)

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
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Type.Equality ((:~:)(..))
import           GHC.Exts (inline)
import           MapPretty ()
import           RefZone (Zone)
import qualified RefZone as RefZone
import           Text.PrettyPrint (isEmpty, fcat, vcat, hcat, punctuate, Doc, ($+$), (<+>), (<>), text)
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)
import           WriterT

text' :: Text -> Doc
text' = text . Text.unpack

data CompositeTag = RecordC | SumC
type RecordT = 'CompositeT 'RecordC
type SumT = 'CompositeT 'SumC
data ASTTag = TypeT | CompositeT CompositeTag

data CompositeTagEquality c
    = IsRecordC !(c :~: 'RecordC)
    | IsSumC !(c :~: 'SumC)

data ASTTagEquality t where
    IsTypeT :: !(t :~: 'TypeT) -> ASTTagEquality t
    IsCompositeT :: !(CompositeTagEquality c) -> !(t :~: 'CompositeT c) -> ASTTagEquality t

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

newtype Identifier = Identifier { _identifierText :: Text }
    deriving (Eq, Ord, Show, NFData, IsString)
instance Pretty Identifier where pPrint = text' . _identifierText

newtype TId = TId { _tid :: Identifier }
    deriving (Eq, Ord, Show, NFData, IsString, Pretty)

newtype GlobalId = GlobalId { _globalId :: Identifier }
    deriving (Eq, Ord, Show, NFData, IsString, Pretty)

newtype Var = Var { _var :: Identifier }
    deriving (Eq, Ord, Show, NFData, IsString, Pretty)

newtype Tag = Tag { _tag :: Identifier }
    deriving (Eq, Ord, Show, NFData, IsString, Pretty)

newtype TParamId = TParamId { _tParamId :: Identifier }
    deriving (Eq, Ord, Show, NFData, IsString, Pretty)

data TypeAST tag ast where
    TFun :: !(ast 'TypeT) -> !(ast 'TypeT) -> TypeAST 'TypeT ast
    TInst :: {-# UNPACK #-}!TId -> !(Map TParamId (ast 'TypeT)) -> TypeAST 'TypeT ast
    TRecord :: !(ast RecordT) -> TypeAST 'TypeT ast
    TSum :: !(ast SumT) -> Type ast
    TEmptyComposite :: IsCompositeTag c => TypeAST ('CompositeT c) ast
    TCompositeExtend ::
        IsCompositeTag c => {-# UNPACK #-}!Tag -> !(ast 'TypeT) ->
        !(ast ('CompositeT c)) -> TypeAST ('CompositeT c) ast

type Type = TypeAST 'TypeT
type Composite c = TypeAST ('CompositeT c)

instance (NFData (ast 'TypeT), NFData (ast RecordT), NFData (ast SumT), NFData (ast tag)) =>
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
ntraverse typ reco su = \case
    TFun a b -> TFun <$> typ a <*> typ b
    TInst n params -> TInst n <$> traverse typ params
    TRecord r -> TRecord <$> reco r
    TSum s -> TSum <$> su s
    TEmptyComposite -> pure TEmptyComposite
    TCompositeExtend n t (r :: ast ('CompositeT c)) ->
        TCompositeExtend n <$> typ t <*>
        case compositeTagRefl :: CompositeTagEquality c of
        IsRecordC Refl -> reco r
        IsSumC Refl -> su r

{-# INLINE typeSubexprs #-}
typeSubexprs ::
    forall f t ast ast'. (Applicative f, IsTag t) =>
    (forall tag. IsTag tag => ast tag -> f (ast' tag)) ->
    TypeAST t ast -> f (TypeAST t ast')
typeSubexprs f = ntraverse f f f

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

instance (Pretty (ast 'TypeT), Pretty (ast RecordT), Pretty (ast SumT)) => Pretty (Type ast) where
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

infixr 2 <+?>
(<+?>) :: Doc -> Doc -> Doc
x <+?> y = fcat [x, " " <> y]

instance (IsCompositeTag c, Pretty (ast 'TypeT), Pretty (ast ('CompositeT c))) => Pretty (Composite c ast) where
    pPrintPrec level prec ast =
        case ast of
        TEmptyComposite -> "{}"
        TCompositeExtend n t r ->
            maybeParens (prec > 1) $
            "{" <+> pPrint n <+> ":" <+> pPrintPrec level 0 t <+> "}" <+?>
            text [compositeChar (Proxy :: Proxy c)] <+> pPrintPrec level 1 r


data Leaf
    = LVar Var
    | LGlobal GlobalId
    | LEmptyRecord
    | LAbsurd
    | LInt Int
    | LHole
    deriving (Show)
instance NFData Leaf where
    rnf (LVar x) = rnf x
    rnf (LGlobal x) = rnf x
    rnf (LInt x) = rnf x
    rnf LEmptyRecord = ()
    rnf LAbsurd = ()
    rnf LHole = ()

instance Pretty Leaf where
    pPrint (LVar x) = pPrint x
    pPrint (LGlobal x) = pPrint x
    pPrint LEmptyRecord = "{}"
    pPrint LAbsurd = "Absurd"
    pPrint (LInt x) = pPrint x
    pPrint LHole = "?"

data Abs v = Abs Var !v
    deriving (Show, Functor, Foldable, Traversable)
instance NFData v => NFData (Abs v) where rnf (Abs a b) = rnf a `seq` rnf b

data App v = App !v !v
    deriving (Show, Functor, Foldable, Traversable)
instance NFData v => NFData (App v) where rnf (App a b) = rnf a `seq` rnf b

data RecExtend v = RecExtend Tag !v !v
    deriving (Show, Functor, Foldable, Traversable)
instance NFData v => NFData (RecExtend v) where rnf (RecExtend a b c) = rnf a `seq` rnf b `seq` rnf c

data Case v = Case Tag !v !v
    deriving (Show, Functor, Foldable, Traversable)
instance NFData v => NFData (Case v) where rnf (Case a b c) = rnf a `seq` rnf b `seq` rnf c

data GetField v = GetField !v Tag
    deriving (Show, Functor, Foldable, Traversable)
instance NFData v => NFData (GetField v) where rnf (GetField a b) = rnf a `seq` rnf b

data Inject v = Inject Tag !v
    deriving (Show, Functor, Foldable, Traversable)
instance NFData v => NFData (Inject v) where rnf (Inject a b) = rnf a `seq` rnf b

data Val v
    = BLam (Abs v)
    | BApp (App v)
    | BRecExtend (RecExtend v)
    | BCase (Case v)
    | BGetField (GetField v)
    | BInject (Inject v)
    | BLeaf Leaf
    deriving (Show, Functor, Foldable, Traversable)

instance NFData v => NFData (Val v) where
    rnf (BLam x) = rnf x
    rnf (BApp x) = rnf x
    rnf (BRecExtend x) = rnf x
    rnf (BCase x) = rnf x
    rnf (BGetField x) = rnf x
    rnf (BInject x) = rnf x
    rnf (BLeaf x) = rnf x

instance Pretty v => Pretty (Val v) where
    pPrintPrec level prec (BLam (Abs name body)) =
        maybeParens (prec > 0) $
        pPrint name <+> "→" <+> pPrintPrec level 0 body
    pPrintPrec level prec (BApp (App func arg)) =
        maybeParens (prec > 9) $
        pPrintPrec level 9 func <+> pPrintPrec level 10 arg
    pPrintPrec level prec (BRecExtend (RecExtend name val rest)) =
        maybeParens (prec > 7) $
        "{" <> pPrint name <> "="
        <> pPrintPrec level 8 val <> "} *"
        <+?> pPrintPrec level 7 rest
    pPrintPrec level prec (BCase (Case name handler restHandler)) =
        maybeParens (prec > 7) $
        "case" <+> pPrint name <+> "→"
        <+> pPrintPrec level 8 handler $+$
        pPrintPrec level 7 restHandler
    pPrintPrec level prec (BGetField (GetField val name)) =
        maybeParens (prec > 8) $
        pPrintPrec level 8 val <> "." <> pPrint name
    pPrintPrec level prec (BInject (Inject name val)) =
        maybeParens (prec > 8) $
        pPrint name <+> pPrintPrec level 8 val
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
instance NFData a => NFData (AV a) where
    rnf (AV ann val) = rnf ann `seq` rnf val

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

lam :: Var -> V -> V
lam name body = V $ BLam $ Abs name body

lambda :: Var -> (V -> V) -> V
lambda name body = lam name $ body $ var $ name

lambdaRecord :: Var -> [Tag] -> ([V] -> V) -> V
lambdaRecord name fields body = lambda name $ \v -> body $ map (v $.) fields

absurd :: V
absurd = V $ BLeaf LAbsurd

case_ :: Tag -> V -> V -> V
case_ name handler restHandlers = V $ BCase $ Case name handler restHandlers

cases :: [(Tag, V)] -> V
cases = foldr (uncurry case_) absurd

litInt :: Int -> V
litInt = V . BLeaf . LInt

hole :: V
hole = V $ BLeaf LHole

infixl 4 $$
($$) :: V -> V -> V
($$) f a = V $ BApp $ App f a

($$:) :: V -> [(Tag, V)] -> V
func $$: fields = func $$ recVal fields

recVal :: [(Tag, V)] -> V
recVal = foldr extend empty
    where
        extend (name, val) rest = V $ BRecExtend (RecExtend name val rest)
        empty = V $ BLeaf LEmptyRecord

($=) :: Tag -> V -> V -> V
(x $= y) z = V $ BRecExtend $ RecExtend x y z

($.) :: V -> Tag -> V
x $. y = V $ BGetField $ GetField x y

(.$) :: Tag -> V -> V
x .$ y = V $ BInject $ Inject x y

var :: Var -> V
var = V . BLeaf . LVar

global :: GlobalId -> V
global = V . BLeaf . LGlobal

infixType :: T 'TypeT -> T 'TypeT -> T 'TypeT -> T 'TypeT
infixType a b c = recordType [("l", a), ("r", b)] ~> c

infixApp :: GlobalId -> V -> V -> V
infixApp name x y = global name $$: [("l", x), ("r", y)]

($+) :: V -> V -> V
($+) = infixApp "+"

($-) :: V -> V -> V
($-) = infixApp "-"

data Constraints tag where
    TypeConstraints :: Constraints 'TypeT
    -- forbidden field set:
    CompositeConstraints :: !(Set Tag) -> Constraints ('CompositeT c)

instance Eq (Constraints tag) where
    (==) a b =
        case a of
        TypeConstraints ->
            case b :: Constraints 'TypeT of
            TypeConstraints -> True
        CompositeConstraints x ->
            -- GADT exhaustiveness checking, ugh!
            case b :: tag ~ 'CompositeT c => Constraints ('CompositeT c) of
            CompositeConstraints y -> x == y

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

data IsBound tag bound
    = Unbound (Constraints tag)
    | Bound bound
    deriving (Functor, Foldable, Traversable)

data UnificationPos tag = UnificationPos
    { __unificationPosNames :: Set (TVarName tag)
      -- TODO: Remove names, use mutable bit/level instead
    , __unificationPosRef :: RefZone.Ref (IsBound tag (UnifiableTypeAST tag))
    }
instance NFData (UnificationPos tag) where rnf (UnificationPos x y) = rnf x `seq` rnf y
instance Pretty (UnificationPos tag) where
    pPrint (UnificationPos names _) = "?" <> pPrint (Set.toList names)

type UnifiableType = UnifiableTypeAST 'TypeT
type UnifiableComposite c = UnifiableTypeAST ('CompositeT c)
data UnifiableTypeAST tag
    = UnifiableTypeVar (UnificationPos tag)
    | UnifiableTypeAST (TypeAST tag UnifiableTypeAST)
instance NFData (UnifiableTypeAST tag) where
    rnf (UnifiableTypeVar x) = rnf x
    rnf (UnifiableTypeAST x) = rnf x
instance Pretty (TypeAST tag UnifiableTypeAST) => Pretty (UnifiableTypeAST tag) where
    pPrint (UnifiableTypeVar pos) = pPrint pos
    pPrint (UnifiableTypeAST t) = pPrint t

Lens.makePrisms ''IsBound
Lens.makeLenses ''UnificationPos

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
        (map pPrintTV (Map.toList tvs) ++
         map pPrintTV (Map.toList rtvs) ++
         map pPrintTV (Map.toList stvs))

instance Pretty (TypeAST tag T) => Pretty (Scheme tag) where
    pPrint (Scheme binders typ)
        | nullBinders binders = pPrint typ
        | otherwise = pPrint binders <> "." <+?> pPrint typ

data Scope = Scope
    { _scopeLocals :: Map Var UnifiableType
    , _scopeGlobals :: Map GlobalId (Scheme 'TypeT)
    }

newScope :: Map GlobalId (Scheme 'TypeT) -> Scope
newScope = Scope Map.empty

emptyScope :: Scope
emptyScope = Scope Map.empty Map.empty

{-# INLINE insertLocal #-}
insertLocal :: Var -> UnifiableType -> Scope -> Scope
insertLocal name typ (Scope locals globals) =
    Scope (Map.insert name typ locals) globals

data Err
    = DoesNotUnify Doc Doc
    | VarNotInScope Var
    | GlobalNotInScope GlobalId
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
        unInfer act $ Env { envFresh = fresh, envZone = zone, envScope = scope }

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

{-# INLINE localScope #-}
localScope :: (Scope -> Scope) -> Infer s a -> Infer s a
localScope f = localEnv $ \e -> e { envScope = f (envScope e) }

{-# INLINE askScope #-}
askScope :: Infer s Scope
askScope = askEnv <&> envScope

{-# INLINE lookupLocal #-}
lookupLocal :: Var -> Infer s (Maybe UnifiableType)
lookupLocal str = askScope <&> _scopeLocals <&> Map.lookup str

{-# INLINE lookupGlobal #-}
lookupGlobal :: GlobalId -> Infer s (Maybe (Scheme 'TypeT))
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

freshPos :: Constraints tag -> Infer s (UnificationPos tag)
freshPos cs =
    do
        tvarName <- freshTVarName
        ref <- Unbound cs & newRef
        UnificationPos (Set.singleton tvarName) ref & return

{-# INLINE freshTVar #-}
freshTVar :: Constraints tag -> Infer s (UnifiableTypeAST tag)
freshTVar cs = freshPos cs <&> UnifiableTypeVar

instantiate :: forall s tag. IsTag tag => Scheme tag -> Infer s (UnifiableTypeAST tag)
instantiate (Scheme (SchemeBinders typeVars recordVars sumVars) typ) =
    {-# SCC "instantiate" #-}
    do
        typeUFs <- {-# SCC "instantiate.freshtvs" #-}traverse freshTVar typeVars
        recordUFs <- {-# SCC "instantiate.freshrtvs" #-}traverse freshTVar recordVars
        sumUFs <- {-# SCC "instantiate.freshstvs" #-}traverse freshTVar sumVars
        let go ::
                Map (TVarName t) (UnifiableTypeAST t) ->
                T t -> Infer s (UnifiableTypeAST t)
            go binders (TVar tvarName) = return (binders Map.! tvarName)
            go _ (T typeAST) =
                ntraverse (go typeUFs) (go recordUFs) (go sumUFs) typeAST
                <&> UnifiableTypeAST
        {-# SCC "instantiate.go" #-}typ & case tagRefl :: ASTTagEquality tag of
            IsTypeT Refl -> go typeUFs
            IsCompositeT (IsRecordC Refl) Refl -> go recordUFs
            IsCompositeT (IsSumC Refl) Refl -> go sumUFs

repr ::
    UnificationPos tag ->
    Infer s (UnificationPos tag, IsBound tag (TypeAST tag UnifiableTypeAST))
repr x =
    do
        zone <- askEnv <&> envZone
        let go pos@(UnificationPos _ ref) =
                RefZone.readRef zone ref >>= \case
                Unbound uCs -> return (pos, Unbound uCs)
                Bound (UnifiableTypeAST ast) -> return (pos, Bound ast)
                Bound (UnifiableTypeVar innerPos) ->
                    do
                        res <- go innerPos
                        -- path compression:
                        RefZone.writeRef zone ref (snd res <&> UnifiableTypeAST)
                        return res
        liftST $ go x

schemeBindersSingleton :: forall tag. IsTag tag => TVarName tag -> Constraints tag -> SchemeBinders
schemeBindersSingleton tvName cs =
    case tagRefl :: ASTTagEquality tag of
    IsTypeT Refl -> mempty { schemeTypeBinders = binders }
    IsCompositeT (IsRecordC Refl) Refl -> mempty { schemeRecordBinders = binders }
    IsCompositeT (IsSumC Refl) Refl -> mempty { schemeSumBinders = binders }
    where
        binders = Map.singleton tvName cs

deref ::
    forall s tag. IsTag tag =>
    Set Int -> UnifiableTypeAST tag -> WriterT SchemeBinders (Infer s) (T tag)
deref visited = \case
    UnifiableTypeAST ast -> ast & typeSubexprs (deref visited) <&> T
    UnifiableTypeVar (UnificationPos names tvRef)
        | _tVarName tvName `Set.member` visited ->
              throwError InfiniteType & lift
        | otherwise ->
            do
                -- TODO: Avoid Infer s monad and use ST directly?
                lift (readRef tvRef) >>= \case
                    Unbound cs ->
                        do
                            tell $ schemeBindersSingleton tvName cs
                            return $ TVar tvName
                    Bound unifiable ->
                        deref (Set.insert (_tVarName tvName) visited) unifiable
        where
            tvName = Set.findMin names

generalize :: UnifiableType -> Infer s (Scheme 'TypeT)
generalize t =
    {-# SCC "generalize" #-}
    deref Set.empty t
    & runWriterT
    <&> uncurry (flip Scheme)

data CompositeTail c
    = CompositeTailClosed
    | CompositeTailOpen (UnificationPos ('CompositeT c)) (Constraints ('CompositeT c))
    -- TODO(Review): The "Constraints" cache above is necessary? Can it become stale?

type CompositeFields = Map Tag UnifiableType

data FlatComposite c = FlatComposite
    { _fcFields :: CompositeFields
    , __fcTailUF :: CompositeTail c
    }

Lens.makeLenses ''FlatComposite

flattenVal :: Composite c UnifiableTypeAST -> Infer s (FlatComposite c)
flattenVal TEmptyComposite =
    return $ FlatComposite Map.empty CompositeTailClosed
flattenVal (TCompositeExtend n t r) =
    flatten r <&> fcFields . Lens.at n ?~ t
    where
        flatten (UnifiableTypeAST ast) = flattenVal ast
        flatten (UnifiableTypeVar pos) =
            repr pos >>= \case
            (_, Unbound cs) -> return $ FlatComposite Map.empty $ CompositeTailOpen pos cs
            (_, Bound ast) -> flattenVal ast

unflatten :: IsCompositeTag c => FlatComposite c -> UnifiableComposite c
unflatten (FlatComposite fields tail) =
    {-# SCC "unflatten" #-}Map.toList fields & go
    where
        go [] = case tail of
            CompositeTailClosed -> UnifiableTypeAST TEmptyComposite
            CompositeTailOpen pos _ -> UnifiableTypeVar pos
        go ((name, typ):fs) =
            go fs & TCompositeExtend name typ & UnifiableTypeAST

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
            CompositeTailOpen (UnificationPos _ ref) innerConstraints ->
                writeRef ref $ Unbound $ outerConstraints `mappend` innerConstraints
    where
        FlatComposite innerFields innerTail = flatComposite

constraintsCheck ::
    Constraints tag -> TypeAST tag UnifiableTypeAST -> Infer s ()
constraintsCheck TypeConstraints _ = return ()
constraintsCheck cs@CompositeConstraints{} inner =
    ({-# SCC "constraintsCheck.flatten" #-}flattenVal inner) >>= flatConstraintsCheck cs

writeCompositeTail ::
    IsCompositeTag c =>
    (UnificationPos ('CompositeT c), Constraints ('CompositeT c)) ->
    FlatComposite c -> Infer s ()
writeCompositeTail (pos, cs) composite =
    do
        {-# SCC "flatConstraintsCheck" #-}flatConstraintsCheck cs composite
        writeRef (__unificationPosRef pos) $ Bound $ unflatten composite

{-# INLINE unifyCompositesOpenClosed #-}
unifyCompositesOpenClosed ::
    IsCompositeTag c =>
    (UnificationPos ('CompositeT c), Constraints ('CompositeT c), CompositeFields) ->
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
    (UnificationPos ('CompositeT c), Constraints ('CompositeT c), CompositeFields) ->
    (UnificationPos ('CompositeT c), Constraints ('CompositeT c), CompositeFields) ->
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
    IsCompositeTag c => UnifiableComposite c -> UnifiableComposite c ->
    Infer s ()
unifyComposite = {-# SCC "unifyComposite" #-}unify unifyCompositeAST

-- We already know we are record vals, and will re-read them
-- via flatten, so no need for unify's read of these:
unifyCompositeAST ::
    IsCompositeTag c =>
    Composite c UnifiableTypeAST ->
    Composite c UnifiableTypeAST ->
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
    (TypeAST tag UnifiableTypeAST ->
     TypeAST tag UnifiableTypeAST -> Infer s ()) ->
    UnifiableTypeAST tag -> UnifiableTypeAST tag -> Infer s ()
unify f (UnifiableTypeAST u) (UnifiableTypeAST v) = f u v
unify f (UnifiableTypeAST u) (UnifiableTypeVar v) = unifyVarAST f u v
unify f (UnifiableTypeVar u) (UnifiableTypeAST v) = unifyVarAST f v u
unify f (UnifiableTypeVar u) (UnifiableTypeVar v) =
    do
        (uPos@(UnificationPos _ uRef), ur) <- repr u
        (vPos@(UnificationPos _ vRef), vr) <- repr v
        -- TODO: Choose which to link into which weight/level-wise
        let link a b =
                -- TODO: Update the "names"? They should die!
                writeRef (__unificationPosRef a) $
                Bound $ UnifiableTypeVar b
        if uRef == vRef
            then return ()
            else case (ur, vr) of
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
    UnificationPos tag -> Constraints tag -> TypeAST tag UnifiableTypeAST ->
    Infer s ()
unifyUnbound pos cs ast =
    do
        {-# SCC "constraintsCheck" #-}constraintsCheck cs ast
        writeRef (__unificationPosRef pos) $ Bound (UnifiableTypeAST ast)

unifyVarAST ::
    (IsTag tag, Monoid (Constraints tag)) =>
    (TypeAST tag UnifiableTypeAST ->
     TypeAST tag UnifiableTypeAST -> Infer s ()) ->
    TypeAST tag UnifiableTypeAST -> UnificationPos tag -> Infer s ()
unifyVarAST f uAst v =
    repr v >>= \case
    (_, Bound vAst) -> f uAst vAst
    (vPos, Unbound vCs) -> unifyUnbound vPos vCs uAst

unifyTInstParams ::
    Err -> Map TParamId UnifiableType -> Map TParamId UnifiableType -> Infer s ()
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

unifyType :: UnifiableType -> UnifiableType -> Infer s ()
unifyType =
    {-# SCC "unifyType" #-}unify f
    where
        f uTyp@(TInst uName uParams) vTyp =
            case vTyp of
            TInst vName vParams | uName == vName ->
                {-# SCC "unifyTInstParams" #-}
                unifyTInstParams err uParams vParams
            _ -> throwError err
            where
                err = DoesNotUnify (pPrint uTyp) (pPrint vTyp)
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

int :: TypeAST 'TypeT ast
int = TInst "Int" Map.empty

type InferResult = (AV UnifiableType, UnifiableType)

inferRes :: Val (AV UnifiableType) -> UnifiableType -> (AV UnifiableType, UnifiableType)
inferRes val typ = (AV typ val, typ)

inferLeaf :: Leaf -> Infer s InferResult
inferLeaf leaf =
    {-# SCC "inferLeaf" #-}
    case leaf of
    LEmptyRecord ->
        {-# SCC "inferEmptyRecord" #-}
        UnifiableTypeAST TEmptyComposite & TRecord & UnifiableTypeAST & return
    LAbsurd ->
        {-# SCC "inferAbsurd" #-}
        do
            res <- freshTVar TypeConstraints
            let emptySum = UnifiableTypeAST TEmptyComposite & TSum & UnifiableTypeAST
            TFun emptySum res & UnifiableTypeAST & return
    LGlobal n ->
        {-# SCC "inferGlobal" #-}
        lookupGlobal n >>= \case
        Just scheme -> instantiate scheme
        Nothing -> throwError $ GlobalNotInScope n
    LInt _ ->
        {-# SCC "inferInt" #-}
        UnifiableTypeAST int & return
    LHole ->
        {-# SCC "inferHole" #-}
        freshTVar TypeConstraints
    LVar n ->
        {-# SCC "inferVar" #-}
        lookupLocal n >>= \case
        Just typ -> return typ
        Nothing -> throwError $ VarNotInScope n
    <&> inferRes (BLeaf leaf)

inferLam :: Abs V -> Infer s InferResult
inferLam (Abs n body) =
    {-# SCC "inferLam" #-}
    do
        nType <- freshTVar TypeConstraints
        (body', resType) <- infer body & localScope (insertLocal n nType)
        TFun nType resType & UnifiableTypeAST
            & inferRes (BLam (Abs n body')) & return

inferApp :: App V -> Infer s InferResult
inferApp (App fun arg) =
    {-# SCC "inferApp" #-}
    do
        (fun', funTyp) <- infer fun
        (arg', argTyp) <- infer arg
        resTyp <- freshTVar TypeConstraints

        let expectedFunTyp = TFun argTyp resTyp & UnifiableTypeAST
        unifyType expectedFunTyp funTyp
        inferRes (BApp (App fun' arg')) resTyp & return

inferRecExtend :: RecExtend V -> Infer s InferResult
inferRecExtend (RecExtend name val rest) =
    {-# SCC "inferRecExtend" #-}
    do
        (val', valTyp) <- infer val
        (rest', restTyp) <- infer rest
        unknownRestFields <- freshTVar $ CompositeConstraints $ Set.singleton name
        let expectedResTyp = TRecord unknownRestFields & UnifiableTypeAST
        unifyType expectedResTyp restTyp
        TCompositeExtend name valTyp unknownRestFields
            & UnifiableTypeAST
            & TRecord & UnifiableTypeAST
            & inferRes (BRecExtend (RecExtend name val' rest'))
            & return

inferCase :: Case V -> Infer s InferResult
inferCase (Case name handler restHandler) =
    {-# SCC "inferCase" #-}
    do
        resType <- freshTVar TypeConstraints
        let toResType x = TFun x resType & UnifiableTypeAST

        fieldType <- freshTVar TypeConstraints

        (handler', handlerTyp) <- infer handler
        (restHandler', restHandlerTyp) <- infer restHandler

        sumTail <- freshTVar $ CompositeConstraints $ Set.singleton name

        let expectedHandlerTyp = toResType fieldType
        unifyType expectedHandlerTyp handlerTyp

        let expectedRestHandlerType = TSum sumTail & UnifiableTypeAST & toResType
        unifyType expectedRestHandlerType restHandlerTyp

        TCompositeExtend name fieldType sumTail
            & UnifiableTypeAST & TSum & UnifiableTypeAST & toResType
            & inferRes (BCase (Case name handler' restHandler'))
            & return

inferGetField :: GetField V -> Infer s InferResult
inferGetField (GetField val name) =
    {-# SCC "inferGetField" #-}
    do
        resTyp <- freshTVar TypeConstraints
        (val', valTyp) <- infer val
        expectedValTyp <-
            freshTVar (CompositeConstraints (Set.singleton name))
            <&> TCompositeExtend name resTyp
            <&> UnifiableTypeAST
            <&> TRecord <&> UnifiableTypeAST
        unifyType expectedValTyp valTyp
        inferRes (BGetField (GetField val' name)) resTyp & return

inferInject :: Inject V -> Infer s InferResult
inferInject (Inject name val) =
    {-# SCC "inferInject" #-}
    do
        (val', valTyp) <- infer val
        freshTVar (CompositeConstraints (Set.singleton name))
            <&> TCompositeExtend name valTyp
            <&> UnifiableTypeAST
            <&> TSum <&> UnifiableTypeAST
            <&> inferRes (BInject (Inject name val'))

infer :: V -> Infer s InferResult
infer (V v) =
    {-# SCC "infer" #-}
    case v of
    BLeaf x -> inferLeaf x
    BLam x -> inferLam x
    BApp x -> inferApp x
    BRecExtend x -> inferRecExtend x
    BGetField x -> inferGetField x
    BInject x -> inferInject x
    BCase x -> inferCase x

inferScheme :: Scope -> V -> Either Err (AV UnifiableType, Scheme 'TypeT)
inferScheme scope x =
    {-# SCC "inferScheme" #-}
    runInfer scope $ infer x >>= inline _2 generalize

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

globals :: Map GlobalId (Scheme 'TypeT)
globals =
    mconcat
    [ "+" ==> intInfix
    , "-" ==> intInfix
    ]
    where
        intInfix = forAll 0 0 0 $ \ [] [] [] -> infixType intType intType intType
        (==>) = Map.singleton

test :: V -> Doc
test x =
    {-# SCC "test" #-}
    pPrint x <+?>
    case inferScheme (newScope globals) x of
    Left err -> "causes type error:" <+> pPrint err
    Right (_, typ) -> " :: " <+> pPrint typ


example1 :: V
example1 = lam "x" $ lam "y" $ var "x" $$ var "y" $$ var "y"

example2 :: V
example2 = lam "x" $ recVal [] & "x" $= var "x" & "y" $= lambda "x" id

example3 :: V
example3 = lam "x" $ (var "x" $. "y") $$ lambda "a" id

example4 :: V
example4 = lam "x" $ var "x" $$ var "x"

example5 :: V
example5 = lam "x" $ (var "x" $. "y") $$ (var "x" $. "y")

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

example9 :: V
example9 =
    cases
    [ ("Nothing", lam "_" (litInt 0))
    , ("Just", lambda "x" $ \x -> litInt 1 $+ x)
    ]

example10 :: V
example10 =
    lambda "f" $ \f ->
    lambda "x" $ \x ->
    (x $. "a")
    $$ (f $$ x)
    $$ (f $$ recVal [("a", hole)])

example11 :: V
example11 =
    lambda "f" $ \f ->
    lambda "x" $ \x ->
    f $$ (x $. "a") $$ x

runTests :: Doc
runTests =
    vcat $ map test
    [ example1
    , example2
    , example3
    , example4
    , example5
    , example6
    , example7
    , example8
    , example9
    , example10
    , example11
    ]
