{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
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
    , Type, Record
    , TypeAST(..), bitraverse, typeSubexprs
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
    , example1, example2, example3, example4, example5, example6, example7, example8, example9, example10
    , runTests
    ) where

import           Prelude.Compat hiding (abs, tail)

import           Data.String (IsString)
import           Control.DeepSeq (NFData(..))
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Lens.Tuple
import           Control.Monad (unless, void, zipWithM_)
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
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Type.Equality ((:~:)(..))
import qualified Data.UnionFind.ZoneRef as UF
import           GHC.Generics (Generic)
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
type Record = TypeAST RecordT
type Composite c = TypeAST ('CompositeT c)

instance (NFData (ast 'TypeT), NFData (ast RecordT), NFData (ast SumT), NFData (ast tag)) =>
         NFData (TypeAST tag ast) where
    rnf (TFun x y) = rnf x `seq` rnf y
    rnf (TInst n params) = rnf n `seq` rnf params
    rnf (TRecord record) = rnf record
    rnf (TSum s) = rnf s
    rnf TEmptyComposite = ()
    rnf (TCompositeExtend n t r) = rnf n `seq` rnf t `seq` rnf r

{-# INLINE bitraverse #-}
bitraverse ::
    Applicative f =>
    (ast 'TypeT -> f (ast' 'TypeT)) ->
    (ast RecordT -> f (ast' RecordT)) ->
    (ast SumT -> f (ast' SumT)) ->
    TypeAST tag ast -> f (TypeAST tag ast')
bitraverse typ reco su = \case
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
typeSubexprs f = bitraverse f f f

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

_TEmptyComposite :: Lens.Prism' (Record a) ()
_TEmptyComposite = Lens.prism' (\() -> TEmptyComposite) $ \case
    TEmptyComposite -> Just ()
    _ -> Nothing

_TCompositeExtend :: Lens.Prism' (Record ast) (Tag, ast 'TypeT, ast RecordT)
_TCompositeExtend = Lens.prism' (\(n, t, r) -> TCompositeExtend n t r) $ \case
    TCompositeExtend n t r -> Just (n, t, r)
    _ -> Nothing

instance (Pretty (ast 'TypeT), Pretty (ast RecordT), Pretty (ast SumT)) => Pretty (Type ast) where
    pPrintPrec level prec ast =
        case ast of
        TFun a b ->
            maybeParens (prec > 0) $
            pPrintPrec level 1 a <+> "->" <+> pPrintPrec level 0 b
        TInst name params -> "#" <> pPrint name <+> pPrint params
        TRecord r -> pPrintPrec level prec r
        TSum s -> pPrintPrec level prec s

instance (IsCompositeTag c, Pretty (ast 'TypeT), Pretty (ast ('CompositeT c))) => Pretty (Composite c ast) where
    pPrintPrec level prec ast =
        case ast of
        TEmptyComposite -> "{}"
        TCompositeExtend n t r ->
            maybeParens (prec > 1) $
            "{" <+> pPrint n <+> ":" <+> pPrintPrec level 0 t <+> "}" <+>
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
        pPrint name <+> "=>" <+> pPrintPrec level 0 body
    pPrintPrec level prec (BApp (App func arg)) =
        maybeParens (prec > 9) $
        pPrintPrec level 9 func <+> pPrintPrec level 10 arg
    pPrintPrec level prec (BRecExtend (RecExtend name val rest)) =
        maybeParens (prec > 7) $
        "{" <> pPrint name <> "="
        <> pPrintPrec level 8 val <+> "} *"
        <+> pPrintPrec level 7 rest
    pPrintPrec level prec (BCase (Case name handler restHandler)) =
        maybeParens (prec > 7) $
        pPrint name <> "->"
        <> pPrintPrec level 8 handler $+$
        "_ ->" <+> pPrintPrec level 7 restHandler
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
    | TVar (TVarName tag)
    deriving (Generic)
instance NFData (T tag)

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

data TypeASTPosition tag = TypeASTPosition
    { __tastPosNames :: Set (TVarName tag)
    , _tastPosType :: Either (Constraints tag) (TypeAST tag UFTypeAST)
    }

type UFType = UFTypeAST 'TypeT
type UFComposite c s = UFTypeAST ('CompositeT c)
newtype UFTypeAST tag = UFTypeAST { tsUF :: UF.Point (TypeASTPosition tag) }
    deriving (NFData)
instance Pretty (UFTypeAST tag) where pPrint _ = ".."

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

data Scope = Scope
    { _scopeLocals :: Map Var UFType
    , _scopeGlobals :: Map GlobalId (Scheme 'TypeT)
    }

newScope :: Map GlobalId (Scheme 'TypeT) -> Scope
newScope = Scope Map.empty

emptyScope :: Scope
emptyScope = Scope Map.empty Map.empty

{-# INLINE insertLocal #-}
insertLocal :: Var -> UFType -> Scope -> Scope
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

{-# INLINE localScope #-}
localScope :: (Scope -> Scope) -> Infer s a -> Infer s a
localScope f = localEnv $ \e -> e { envScope = f (envScope e) }

{-# INLINE askScope #-}
askScope :: Infer s Scope
askScope = askEnv <&> envScope

{-# INLINE lookupLocal #-}
lookupLocal :: Var -> Infer s (Maybe UFType)
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

{-# INLINE newPosition #-}
newPosition ::
    Either (Constraints tag) (TypeAST tag UFTypeAST) ->
    Infer s (UFTypeAST tag)
newPosition t =
    do
        tvarName <- freshTVarName
        zone <- askEnv <&> envZone
        TypeASTPosition (Set.singleton tvarName) t
            & liftST . UF.fresh zone <&> UFTypeAST

{-# INLINE freshTVar #-}
freshTVar :: Constraints tag -> Infer s (UFTypeAST tag)
freshTVar = newPosition . Left

{-# INLINE wrap #-}
wrap :: TypeAST tag UFTypeAST -> Infer s (UFTypeAST tag)
wrap = newPosition . Right

instantiate :: forall s tag. IsTag tag => Scheme tag -> Infer s (UFTypeAST tag)
instantiate (Scheme (SchemeBinders typeVars recordVars sumVars) typ) =
    do
        typeUFs <- traverse freshTVar typeVars
        recordUFs <- traverse freshTVar recordVars
        sumUFs <- traverse freshTVar sumVars
        let lookupTVar :: forall t. IsTag t => TVarName t -> UFTypeAST t
            lookupTVar tvar =
                case tagRefl :: ASTTagEquality t of
                IsTypeT Refl -> typeUFs Map.! tvar
                IsCompositeT (IsRecordC Refl) Refl -> recordUFs Map.! tvar
                IsCompositeT (IsSumC Refl) Refl -> sumUFs Map.! tvar
        let go :: forall t. IsTag t => T t -> Infer s (UFTypeAST t)
            go (TVar tvarName) = return (lookupTVar tvarName)
            go (T typeAST) = typeSubexprs go typeAST >>= wrap
        go typ

getWrapper :: UFTypeAST tag -> Infer s (TypeASTPosition tag)
getWrapper (UFTypeAST r) =
    do
        zone <- askEnv <&> envZone
        UF.descriptor zone r & liftST

deref ::
    forall s tag. IsTag tag =>
    Set Int ->
    UFTypeAST tag -> WriterT SchemeBinders (Infer s) (T tag)
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

generalize :: UFType -> Infer s (Scheme 'TypeT)
generalize t =
    deref Set.empty t
    & runWriterT
    <&> uncurry (flip Scheme)

unifyMatch :: Pretty v => Doc -> v -> Lens.Getting (Monoid.First a) v a -> Infer s a
unifyMatch expected vTyp prism =
    case vTyp ^? prism of
    Nothing -> throwError $ DoesNotUnify expected (pPrint vTyp)
    Just vcontent -> return vcontent

data CompositeTailType = CompositeTailOpen | CompositeTailClosed
type CompositeFields s = Map Tag UFType

data FlatComposite c s = FlatComposite
    { __fcTailUF :: UFComposite c s
    , _fcFields :: CompositeFields s
    , __fcTailType :: CompositeTailType
    , __fcTailConstraints :: Constraints ('CompositeT c)
    }

Lens.makeLenses ''FlatComposite

flattenVal :: UFComposite c s -> Composite c UFTypeAST -> Infer s (FlatComposite c s)
flattenVal uf TEmptyComposite = return $ FlatComposite uf Map.empty CompositeTailClosed mempty
flattenVal _ (TCompositeExtend n t r) =
    flatten r <&> fcFields . Lens.at n ?~ t
    where
        flatten ts =
            getWrapper ts <&> _tastPosType >>= \case
            Left cs -> return $ FlatComposite ts Map.empty CompositeTailOpen cs
            Right typ -> flattenVal ts typ

unflatten ::
    IsCompositeTag c => UFComposite c s -> CompositeFields s -> Infer s (UFComposite c s)
unflatten tail fields =
    Map.toList fields & go
    where
        go [] = return tail
        go ((name, typ):fs) = go fs <&> TCompositeExtend name typ >>= wrap

prettyFieldNames :: Map Tag a -> Doc
prettyFieldNames = intercalate " " . map pPrint . Map.keys

{-# INLINE unifyClosedComposites #-}
unifyClosedComposites :: CompositeFields s -> CompositeFields s -> Infer s ()
unifyClosedComposites uFields vFields
    | Map.keysSet uFields == Map.keysSet vFields = return ()
    | otherwise =
          throwError $
          DoesNotUnify
          ("Record fields:" <+> prettyFieldNames uFields)
          ("Record fields:" <+> prettyFieldNames vFields)

{-# INLINE unifyOpenComposite #-}
unifyOpenComposite ::
    IsCompositeTag c => FlatComposite c s -> FlatComposite c s -> Infer s ()
unifyOpenComposite uOpen vClosed
    | Map.null uniqueUFields =
          do
              tailVal <- unflatten vTail uniqueVFields
              unify (\_ _ -> return ()) uTail tailVal
    | otherwise =
          throwError $
          DoesNotUnify
          ("Record with at least fields:" <+> prettyFieldNames uFields)
          ("Record fields:" <+> prettyFieldNames vFields)

    where
        FlatComposite uTail uFields _ _ = uOpen
        FlatComposite vTail vFields _ _ = vClosed
        uniqueUFields = uFields `Map.difference` vFields
        uniqueVFields = vFields `Map.difference` uFields

{-# INLINE unifyOpenComposites #-}
unifyOpenComposites ::
    IsCompositeTag c => FlatComposite c s -> FlatComposite c s -> Infer s ()
unifyOpenComposites u v =
    do
        commonRest <- freshTVar $ uConstraints `mappend` vConstraints
        uRest <- unflatten commonRest uniqueVFields
        vRest <- unflatten commonRest uniqueUFields
        unifyComposite uTail uRest
        unifyComposite vTail vRest
    where
        FlatComposite uTail uFields _ uConstraints = u
        FlatComposite vTail vFields _ vConstraints = v
        uniqueUFields = uFields `Map.difference` vFields
        uniqueVFields = vFields `Map.difference` uFields

unifyComposite :: IsCompositeTag c => UFComposite c s -> UFComposite c s -> Infer s ()
unifyComposite uUf vUf =
    unify f uUf vUf
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
                uFlat@(FlatComposite _ uFields uType _) <- flattenVal uUf u
                vFlat@(FlatComposite _ vFields vType _) <- flattenVal vUf v
                Map.intersectionWith unifyType uFields vFields
                    & sequenceA_
                case (uType, vType) of
                    (CompositeTailClosed, CompositeTailClosed) -> unifyClosedComposites uFields vFields
                    (CompositeTailOpen  , CompositeTailClosed) -> unifyOpenComposite uFlat vFlat
                    (CompositeTailClosed, CompositeTailOpen  ) -> unifyOpenComposite vFlat uFlat
                    (CompositeTailOpen  , CompositeTailOpen  ) -> unifyOpenComposites uFlat vFlat

constraintsCheck ::
    Constraints tag -> UFTypeAST tag -> TypeAST tag UFTypeAST -> Infer s ()
constraintsCheck TypeConstraints _ _ = return ()
constraintsCheck outerConstraints@(CompositeConstraints outerDisallowed) innerUF inner =
    do
        FlatComposite innerTail innerFields innerTailType innerConstraints <-
            flattenVal innerUF inner
        let duplicates = Set.intersection (Map.keysSet innerFields) outerDisallowed
        unless (Set.null duplicates) $ throwError $ DuplicateFields $
            Set.toList duplicates
        case innerTailType of
            CompositeTailClosed -> return ()
            CompositeTailOpen ->
                setConstraints innerTail (outerConstraints `mappend` innerConstraints)

setConstraints :: Monoid (Constraints tag) => UFTypeAST tag -> Constraints tag -> Infer s ()
setConstraints u constraints =
    do
        zone <- askEnv <&> envZone
        UF.modifyDescriptor zone (tsUF u) (tastPosType . Lens._Left <>~ constraints)
            & liftST & void

unify ::
    (IsTag tag, Monoid (Constraints tag)) =>
    (TypeAST tag UFTypeAST ->
     TypeAST tag UFTypeAST -> Infer s ()) ->
    UFTypeAST tag -> UFTypeAST tag -> Infer s ()
unify f u v =
    do
        zone <- askEnv <&> envZone
        UF.union' zone (tsUF u) (tsUF v) g
            & liftST
            >>= maybe (return ()) id
    where
        g (TypeASTPosition uNames uMTyp) (TypeASTPosition vNames vMTyp) =
            case (uMTyp, vMTyp) of
            (Left uCs, Left vCs) -> (Left (uCs `mappend` vCs), return ())
            (Left uCs, Right y) -> (Right y, constraintsCheck uCs v y)
            (Right x, Left vCs) -> (Right x, constraintsCheck vCs u x)
            (Right x, Right y) -> (Right x, f x y)
            & _1 %~ TypeASTPosition (uNames `mappend` vNames)

unifyTInstParams ::
    Err -> Map TParamId UFType -> Map TParamId UFType -> Infer s ()
unifyTInstParams err uParams vParams
    | uSize /= vSize = throwError err
    | uSize == 0 = return ()
    | otherwise =
        zipWithM_ unifyParam (Map.toAscList uParams) (Map.toAscList vParams)
    where
        uSize = Map.size uParams
        vSize = Map.size vParams
        unifyParam (_, uParam) (_, vParam) = unifyType uParam vParam

unifyType :: UFType -> UFType -> Infer s ()
unifyType =
    unify f
    where
        f uTyp@(TInst uName uParams) vTyp =
            case vTyp of
            TInst vName vParams | uName == vName ->
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

type InferResult = (AV UFType, UFType)

inferRes :: Val (AV UFType) -> UFType -> (AV UFType, UFType)
inferRes val typ = (AV typ val, typ)

inferLeaf :: Leaf -> Infer s InferResult
inferLeaf leaf =
    case leaf of
    LEmptyRecord -> wrap TEmptyComposite >>= wrap . TRecord
    LAbsurd ->
        do
            res <- freshTVar TypeConstraints
            emptySum <- wrap TEmptyComposite >>= wrap . TSum
            TFun emptySum res & wrap
    LGlobal n ->
        lookupGlobal n >>= \case
        Just scheme -> instantiate scheme
        Nothing -> throwError $ GlobalNotInScope n
    LInt _ -> int & wrap
    LHole -> freshTVar TypeConstraints
    LVar n ->
        lookupLocal n >>= \case
        Just typ -> return typ
        Nothing -> throwError $ VarNotInScope n
    <&> inferRes (BLeaf leaf)

inferLam :: Abs V -> Infer s InferResult
inferLam (Abs n body) =
    do
        nType <- freshTVar TypeConstraints
        (body', resType) <- infer body & localScope (insertLocal n nType)
        TFun nType resType & wrap
            <&> inferRes (BLam (Abs n body'))

inferApp :: App V -> Infer s InferResult
inferApp (App fun arg) =
    do
        (fun', funTyp) <- infer fun
        (arg', argTyp) <- infer arg
        resTyp <- freshTVar TypeConstraints

        expectedFunTyp <- TFun argTyp resTyp & wrap
        unifyType expectedFunTyp funTyp
        inferRes (BApp (App fun' arg')) resTyp & return

inferRecExtend :: RecExtend V -> Infer s InferResult
inferRecExtend (RecExtend name val rest) =
    do
        (val', valTyp) <- infer val
        (rest', restTyp) <- infer rest
        unknownRestFields <- freshTVar $ CompositeConstraints $ Set.singleton name
        expectedResTyp <- TRecord unknownRestFields & wrap
        unifyType expectedResTyp restTyp
        TCompositeExtend name valTyp unknownRestFields
            & wrap
            >>= wrap . TRecord
            <&> inferRes (BRecExtend (RecExtend name val' rest'))

inferCase :: Case V -> Infer s InferResult
inferCase (Case name handler restHandler) =
    do
        resType <- freshTVar TypeConstraints
        let toResType x = TFun x resType & wrap

        fieldType <- freshTVar TypeConstraints

        (handler', handlerTyp) <- infer handler
        (restHandler', restHandlerTyp) <- infer restHandler

        sumTail <- freshTVar $ CompositeConstraints $ Set.singleton name

        expectedHandlerTyp <- toResType fieldType
        unifyType expectedHandlerTyp handlerTyp

        expectedRestHandlerType <- TSum sumTail & wrap >>= toResType
        unifyType expectedRestHandlerType restHandlerTyp

        TCompositeExtend name fieldType sumTail
            & wrap <&> TSum >>= wrap >>= toResType
            <&> inferRes (BCase (Case name handler' restHandler'))

inferGetField :: GetField V -> Infer s InferResult
inferGetField (GetField val name) =
    do
        resTyp <- freshTVar TypeConstraints
        (val', valTyp) <- infer val
        expectedValTyp <-
            freshTVar (CompositeConstraints (Set.singleton name))
            <&> TCompositeExtend name resTyp
            >>= wrap
            >>= wrap . TRecord
        unifyType expectedValTyp valTyp
        inferRes (BGetField (GetField val' name)) resTyp & return

inferInject :: Inject V -> Infer s InferResult
inferInject (Inject name val) =
    do
        (val', valTyp) <- infer val
        freshTVar (CompositeConstraints (Set.singleton name))
            <&> TCompositeExtend name valTyp
            >>= wrap
            >>= wrap . TSum
            <&> inferRes (BInject (Inject name val'))

infer :: V -> Infer s InferResult
infer (V v) =
    case v of
    BLeaf x -> inferLeaf x
    BLam x -> inferLam x
    BApp x -> inferApp x
    BRecExtend x -> inferRecExtend x
    BGetField x -> inferGetField x
    BInject x -> inferInject x
    BCase x -> inferCase x

inferScheme :: Scope -> V -> Either Err (AV UFType, Scheme 'TypeT)
inferScheme scope x = runInfer scope $ infer x >>= _2 %%~ generalize

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

(<+?>) :: Doc -> Doc -> Doc
x <+?> y = fcat [x, " ", y]

test :: V -> Doc
test x =
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
    ]
