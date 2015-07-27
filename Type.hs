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

    , ASTTag(..)
    , TypeAST(..), bitraverse, typeSubexprs
    , SchemeBinders(..)
    , Scheme(..)

    , T(..), V(..), AV(..)

    , recordType, recordFrom, (~>), tInst
    , intType, boolType
    , lam, lambda, lambdaRecord
    , recVal, global, litInt
    , ($$), ($=), ($.), ($+), ($-), ($$:)

    , forAll
    , test
    , example1, example2, example3, example4, example5, example6, example7
    , runTests
    ) where

import           Data.STRef
import           Prelude.Compat hiding (abs)

import           Control.DeepSeq (NFData(..))
import           Data.Type.Equality
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
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.String (IsString(..))
import           GHC.Generics (Generic)
import           MapPretty ()
import           Text.PrettyPrint (isEmpty, fcat, hcat, punctuate, Doc, (<+>), (<>), text)
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)
import           UF (UF)
import qualified UF as UF
import           WriterT

data ASTTag = TypeT | RecordT
type Type = TypeAST 'TypeT
type Record = TypeAST 'RecordT

data ASTTagEquality t
    = IsTypeT (t :~: 'TypeT)
    | IsRecordT (t :~: 'RecordT)

class IsTag t where tagRefl :: ASTTagEquality t
instance IsTag 'TypeT where tagRefl = IsTypeT Refl
instance IsTag 'RecordT where tagRefl = IsRecordT Refl

newtype TVarName (tag :: ASTTag) = TVarName { _tVarName :: Int }
    deriving (Eq, Ord, Show, Pretty, NFData)

data TypeAST tag ast where
    TFun :: !(ast 'TypeT) -> !(ast 'TypeT) -> Type ast
    TInst :: String -> Type ast
    TRecord :: !(ast 'RecordT) -> Type ast
    TEmptyRecord :: Record ast
    TRecExtend :: String -> !(ast 'TypeT) -> !(ast 'RecordT) -> Record ast

instance (NFData (ast 'TypeT), NFData (ast 'RecordT)) => NFData (TypeAST tag ast) where
    rnf (TFun x y) = rnf x `seq` rnf y
    rnf (TInst n) = rnf n
    rnf (TRecord record) = rnf record
    rnf TEmptyRecord = ()
    rnf (TRecExtend n t r) = rnf n `seq` rnf t `seq` rnf r

bitraverse ::
    Applicative f =>
    (ast 'TypeT -> f (ast' 'TypeT)) ->
    (ast 'RecordT -> f (ast' 'RecordT)) ->
    TypeAST tag ast -> f (TypeAST tag ast')
bitraverse typ reco = \case
    TFun a b -> TFun <$> typ a <*> typ b
    TInst n -> pure (TInst n)
    TRecord r -> TRecord <$> reco r
    TEmptyRecord -> pure TEmptyRecord
    TRecExtend n t r -> TRecExtend n <$> typ t <*> reco r

typeSubexprs ::
    Applicative f => (forall tag. IsTag tag => ast tag -> f (ast' tag)) -> TypeAST t ast -> f (TypeAST t ast')
typeSubexprs f = bitraverse f f

_TFun :: Lens.Prism' (TypeAST 'TypeT ast) (ast 'TypeT, ast 'TypeT)
_TFun = Lens.prism' (uncurry TFun) $ \case
    TFun x y -> Just (x, y)
    _ -> Nothing

_TInst :: Lens.Prism' (Type a) String
_TInst = Lens.prism' TInst $ \case
    TInst n -> Just n
    _ -> Nothing

_TRecord :: Lens.Prism' (Type ast) (ast 'RecordT)
_TRecord = Lens.prism' TRecord $ \case
    TRecord n -> Just n
    _ -> Nothing

_TEmptyRecord :: Lens.Prism' (Record a) ()
_TEmptyRecord = Lens.prism' (\() -> TEmptyRecord) $ \case
    TEmptyRecord -> Just ()
    _ -> Nothing

_TRecExtend :: Lens.Prism' (Record ast) (String, ast 'TypeT, ast 'RecordT)
_TRecExtend = Lens.prism' (\(n, t, r) -> TRecExtend n t r) $ \case
    TRecExtend n t r -> Just (n, t, r)
    _ -> Nothing

instance (Pretty (ast 'TypeT), Pretty (ast 'RecordT)) => Pretty (TypeAST tag ast) where
    pPrintPrec level prec ast =
        case ast of
        TFun a b ->
            maybeParens (prec > 0) $
            pPrintPrec level 1 a <+> "->" <+> pPrintPrec level 0 b
        TInst name -> "#" <> text name
        TRecord r -> pPrintPrec level prec r
        TEmptyRecord -> "{}"
        TRecExtend n t r -> "{" <+> text n <+> ":" <+> pPrint t <+> "} *" <+> pPrint r

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

data Val v
    = BLam (Abs v)
    | BApp (App v)
    | BRecExtend (RecExtend v)
    | BGetField (GetField v)
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

instance Pretty (T tag) where
    pPrintPrec level prec (T typ) = pPrintPrec level prec typ
    pPrintPrec _ _ (TVar name) = text "a" <> pPrint name

infixr 4 ~>
(~>) :: T 'TypeT -> T 'TypeT -> T 'TypeT
a ~> b = T $ TFun a b

recordFrom :: [(String, T 'TypeT)] -> T 'RecordT
recordFrom [] = T TEmptyRecord
recordFrom ((name, typ):fs) = T $ TRecExtend name typ $ recordFrom fs

recordType :: [(String, T 'TypeT)] -> T 'TypeT
recordType = T . TRecord . recordFrom

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
    RecordConstraints :: !(Set String) -> Constraints 'RecordT

instance NFData (Constraints tag) where
    rnf TypeConstraints = ()
    rnf (RecordConstraints cs) = rnf cs

instance Monoid (Constraints 'TypeT) where
    mempty = TypeConstraints
    mappend _ _ = TypeConstraints

instance Monoid (Constraints 'RecordT) where
    mempty = RecordConstraints mempty
    mappend (RecordConstraints x) (RecordConstraints y) =
        RecordConstraints (x `mappend` y)

data TypeASTPosition s tag = TypeASTPosition
    { __tastPosNames :: Set (TVarName tag)
    , _tastPosType :: Either (Constraints tag) (TypeAST tag (UFTypeAST s))
    }

type UFType s = UFTypeAST s 'TypeT
type UFRecord s = UFTypeAST s 'RecordT
newtype UFTypeAST s tag = TS { tsUF :: UF s (TypeASTPosition s tag) }
instance Pretty (UFTypeAST s tag) where
    pPrint _ = ".."

Lens.makeLenses ''TypeASTPosition

type TVarBinders tag = Map (TVarName tag) (Constraints tag)

data SchemeBinders = SchemeBinders
    { schemeTypeBinders :: TVarBinders 'TypeT
    , schemeRecordBinders :: TVarBinders 'RecordT
    } deriving (Generic)
instance NFData SchemeBinders
instance Monoid SchemeBinders where
    mempty = SchemeBinders Map.empty Map.empty
    mappend (SchemeBinders t0 r0) (SchemeBinders t1 r1) =
        SchemeBinders
        (Map.unionWith mappend t0 t1)
        (Map.unionWith mappend r0 r1)

nullBinders :: SchemeBinders -> Bool
nullBinders (SchemeBinders a b) = Map.null a && Map.null b

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
        suffix (RecordConstraints cs) =
            "∉" <> (intercalate " " . map pPrint) (Set.toList cs)

instance Pretty SchemeBinders where
    pPrint (SchemeBinders tvs rtvs) =
        intercalate " " $
        (map pPrintTV (Map.toList tvs) ++
         map pPrintTV (Map.toList rtvs))

instance Pretty (Scheme tag) where
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
            & liftST . UF.new <&> TS

{-# INLINE freshTVar #-}
freshTVar :: Constraints tag -> Infer s (UFTypeAST s tag)
freshTVar = newPosition . Left

{-# INLINE wrap #-}
wrap :: TypeAST tag (UFTypeAST s) -> Infer s (UFTypeAST s tag)
wrap = newPosition . Right

instantiate :: forall s tag. IsTag tag => Scheme tag -> Infer s (UFTypeAST s tag)
instantiate (Scheme (SchemeBinders typeVars recordVars) typ) =
    do
        typeUFs <- traverse freshTVar typeVars
        recordUFs <- traverse freshTVar recordVars
        let lookupTVar :: forall t. IsTag t => TVarName t -> UFTypeAST s t
            lookupTVar tvar =
                case tagRefl :: ASTTagEquality t of
                IsTypeT Refl -> typeUFs Map.! tvar
                IsRecordT Refl -> recordUFs Map.! tvar
        let go :: forall t. IsTag t => T t -> Infer s (UFTypeAST s t)
            go (TVar tvarName) = return (lookupTVar tvarName)
            go (T typeAST) = typeSubexprs go typeAST >>= wrap
        go typ

getWrapper :: UFTypeAST s tag -> Infer s (TypeASTPosition s tag)
getWrapper (TS r) = UF.find r & liftST

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
                IsTypeT Refl -> mempty { schemeTypeBinders = Map.singleton tvName cs }
                IsRecordT Refl -> mempty { schemeRecordBinders = Map.singleton tvName cs }
            return $ TVar tvName
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

type RecordTail s = UFRecord s
type RecordFields s = Map String (UFType s)
type ClosedRecord s = RecordFields s
type OpenRecord s = (RecordFields s, RecordTail s)

data FlatRecord s = FlatRecord
    { __frMTail :: Maybe (RecordTail s)
    , _frFields :: RecordFields s
    }

Lens.makeLenses ''FlatRecord

flattenVal :: Record (UFTypeAST s) -> Infer s (FlatRecord s)
flattenVal TEmptyRecord = return $ FlatRecord Nothing Map.empty
flattenVal (TRecExtend n t r) =
    flatten r <&> frFields . Lens.at n ?~ t
    where
        flatten ts =
            getWrapper ts <&> _tastPosType >>= \case
            Left _ -> return $ FlatRecord (Just ts) Map.empty
            Right typ -> flattenVal typ

unflatten :: FlatRecord s -> Infer s (UFRecord s)
unflatten (FlatRecord mTail fields) =
    Map.toList fields & go
    where
        go [] =
            case mTail of
            Nothing -> wrap TEmptyRecord
            Just tailVal -> return tailVal
        go ((name, typ):fs) = go fs <&> TRecExtend name typ >>= wrap

unifyClosedRecords :: ClosedRecord s -> ClosedRecord s -> Infer s ()
unifyClosedRecords uFields vFields
    | Map.keysSet uFields == Map.keysSet vFields = return ()
    | otherwise =
          throwError $
          DoesNotUnify
          ("Record fields:" <+> pPrint (Map.keys uFields))
          ("Record fields:" <+> pPrint (Map.keys vFields))

unifyOpenRecord :: OpenRecord s -> ClosedRecord s -> Infer s ()
unifyOpenRecord (uFields, uTail) vFields
    | Map.null uniqueUFields =
          do
              tailVal <- unflatten $ FlatRecord Nothing uniqueVFields
              unify (\_ _ -> return ()) uTail tailVal
    | otherwise =
          throwError $
          DoesNotUnify
          ("Record with at least fields:" <+> pPrint (Map.keys uFields))
          ("Record fields:" <+> pPrint (Map.keys vFields))

    where
        uniqueUFields = uFields `Map.difference` vFields
        uniqueVFields = vFields `Map.difference` uFields

unifyOpenRecords :: OpenRecord s -> OpenRecord s -> Infer s ()
unifyOpenRecords (uFields, uTail) (vFields, vTail) =
    do
        commonRest <-
            freshTVar $ RecordConstraints $
            Map.keysSet uFields `Set.union`
            Map.keysSet vFields
        uRest <- FlatRecord (Just commonRest) uniqueVFields & unflatten
        vRest <- FlatRecord (Just commonRest) uniqueUFields & unflatten
        unifyRecord uTail uRest
        unifyRecord vTail vRest
    where
        uniqueUFields = uFields `Map.difference` vFields
        uniqueVFields = vFields `Map.difference` uFields

unifyRecord :: UFRecord s -> UFRecord s -> Infer s ()
unifyRecord =
    unify f
    where
        -- We already know we are record vals, and will re-read them
        -- via flatten, so no need for unify's read of these:
        f TEmptyRecord TEmptyRecord = return ()
        f (TRecExtend un ut ur) (TRecExtend vn vt vr)
            | un == vn =
            do
                unifyType ut vt
                unifyRecord ur vr
        f u v =
            do
                FlatRecord uMTail uFields <- flattenVal u
                FlatRecord vMTail vFields <- flattenVal v
                Map.intersectionWith unifyType uFields vFields
                    & sequenceA_
                case (uMTail, vMTail) of
                    (Nothing, Nothing) -> unifyClosedRecords uFields vFields
                    (Just uTail, Nothing) -> unifyOpenRecord (uFields, uTail) vFields
                    (Nothing, Just vTail) -> unifyOpenRecord (vFields, vTail) uFields
                    (Just uTail, Just vTail) -> unifyOpenRecords (uFields, uTail) (vFields, vTail)

constraintsCheck :: Constraints tag -> TypeAST tag (UFTypeAST s) -> Infer s ()
constraintsCheck TypeConstraints _ = return ()
constraintsCheck old@(RecordConstraints names) r =
    do
        FlatRecord mTail fields <- flattenVal r
        let fieldsSet = Map.keysSet fields
        let forbidden = Set.intersection fieldsSet names
        unless (Set.null forbidden) $ throwError $ DuplicateFields $
            Set.toList forbidden
        case mTail of
            Nothing -> return ()
            Just rTail -> setConstraints rTail (old `mappend` RecordConstraints fieldsSet)

setConstraints :: Monoid (Constraints tag) => UFTypeAST s tag -> Constraints tag -> Infer s ()
setConstraints u constraints =
    UF.modify (tsUF u) (tastPosType . Lens._Left <>~ constraints) & liftST & void

unify ::
    (IsTag tag, Monoid (Constraints tag)) =>
    (TypeAST tag (UFTypeAST s) ->
     TypeAST tag (UFTypeAST s) -> Infer s ()) ->
    UFTypeAST s tag -> UFTypeAST s tag -> Infer s ()
unify f u v =
    UF.union g (tsUF u) (tsUF v)
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
                unifyRecord uRec vRec
        f (TFun uArg uRes) vTyp =
            do
                (vArg, vRes) <- unifyMatch "TFun" vTyp _TFun
                unifyType uArg vArg
                unifyType uRes vRes

inferLeaf :: Scope s -> Leaf -> Infer s (UFType s)
inferLeaf scope leaf =
    case leaf of
    LEmptyRecord -> wrap TEmptyRecord >>= wrap . TRecord
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
        unknownRestFields <- freshTVar $ RecordConstraints $ Set.singleton name
        expectedResTyp <- TRecord unknownRestFields & wrap
        unifyType expectedResTyp restTyp
        TRecExtend name valTyp unknownRestFields
            & wrap
            >>= wrap . TRecord

inferGetField :: Scope s -> GetField V -> Infer s (UFType s)
inferGetField scope (GetField val name) =
    do
        resTyp <- freshTVar TypeConstraints
        valTyp <- infer scope val
        expectedValTyp <-
            freshTVar (RecordConstraints (Set.singleton name))
            <&> TRecExtend name resTyp
            >>= wrap
            >>= wrap . TRecord
        unifyType expectedValTyp valTyp
        return resTyp

infer :: Scope s -> V -> Infer s (UFType s)
infer scope (V v) =
    case v of
    BLeaf l -> inferLeaf scope l
    BLam abs -> inferLam scope abs
    BApp app -> inferApp scope app
    BRecExtend ext -> inferRecExtend scope ext
    BGetField ext -> inferGetField scope ext

inferScheme :: (forall s. Scope s) -> V -> Either Err (Scheme 'TypeT)
inferScheme scope x = runInfer $ infer scope x >>= generalize

forAll :: Int -> Int -> ([T 'TypeT] -> [T 'RecordT] -> T tag) -> Scheme tag
forAll nTvs nRtvs mkType =
    Scheme (SchemeBinders cTvs cRtvs) $ mkType (map TVar tvs) (map TVar rtvs)
    where
        cTvs = Map.fromList [ (tv, mempty) | tv <- tvs ]
        cRtvs = Map.fromList [ (tv, mempty) | tv <- rtvs ]
        tvs = map TVarName [1..nTvs]
        rtvs = map TVarName [nTvs+1..nTvs+nRtvs]

globals :: Map String (Scheme 'TypeT)
globals =
    mconcat
    [ "+" ==> intInfix
    , "-" ==> intInfix
    ]
    where
        intInfix = forAll 0 0 $ \ [] [] -> infixType intType intType intType
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
    ]
