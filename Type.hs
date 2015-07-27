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
module Main
    ( Infer, runInfer, inferScheme
    , TypeAST(..), bitraverse, typeSubexprs
    , SchemeBinders(..)
    , Scheme(..)
    , Err(..)
    , V(..), lam, ($$), recVal, ($=), ($.)
    , infer
    , test, example1, example2, example3, example4, example5, example6
    , main
    ) where

import           Data.Type.Equality
import           Prelude.Compat hiding (abs)

import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Lens.Tuple
import           Control.Monad (unless, (>=>))
import           Control.Monad.ST (ST, runST)
import           Control.Monad.State (StateT, evalStateT, modify, get)
import           Control.Monad.Trans.Class (lift)
import           Control.Monad.Trans.Either
import           Data.Foldable (sequenceA_)
import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Monoid as Monoid
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.String (IsString(..))
import           MapPretty ()
import           Text.PrettyPrint (hcat, punctuate, Doc, (<+>), (<>), text)
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)
import           UF (UF)
import qualified UF as UF
import           WriterT

newtype Const a (b :: k) = Const { getConst :: a }
    deriving (Eq, Ord, Read, Show, Functor)

instance Monoid a => Applicative (Const a) where
    pure _ = Const mempty
    Const x <*> Const y = Const (mappend x y)

data ASTTag = TypeT | RecordT
type Type = TypeAST 'TypeT
type Record = TypeAST 'RecordT

data ASTTagHandlers f = ASTTagHandlers
    { atpType :: f 'TypeT
    , atpRecord :: f 'RecordT
    }

data ASTTagEquality t
    = IsTypeT (t :~: 'TypeT)
    | IsRecordT (t :~: 'RecordT)

class IsTag t where
    caseTagOf :: ASTTagHandlers f -> f t
    tagRefl :: ASTTagEquality t

instance IsTag 'TypeT where
    caseTagOf = atpType
    tagRefl = IsTypeT Refl

instance IsTag 'RecordT where
    caseTagOf = atpRecord
    tagRefl = IsRecordT Refl

newtype TVarName (tag :: ASTTag) = TVarName { _tVarName :: Int }
    deriving (Eq, Ord, Show, Pretty)

data TypeAST tag ast where
    TFun :: !(ast 'TypeT) -> !(ast 'TypeT) -> Type ast
    TInst :: String -> Type ast
    TRecord :: ast 'RecordT -> Type ast
    TEmptyRecord :: Record ast
    TRecExtend :: String -> ast 'TypeT -> ast 'RecordT -> Record ast

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

typeSubexprsList :: TypeAST tag ast -> ([ast 'TypeT], [ast 'RecordT])
typeSubexprsList =
    getConst . bitraverse
    (\typ -> Const ([typ], []))
    (\reco -> Const ([], [reco]))

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
    deriving (Show)

instance Pretty Leaf where
    pPrint (LVar x) = text x
    pPrint (LGlobal x) = text x
    pPrint LEmptyRecord = "{}"

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

data T tag
    = T (TypeAST tag T)
    | TVar (TVarName tag)

instance Pretty (T tag) where
    pPrintPrec level prec (T typ) = pPrintPrec level prec typ
    pPrintPrec _ _ (TVar name) = text "a" <> pPrint name

lam :: String -> V -> V
lam name body = V $ BLam $ Abs name body

infixl 4 $$
($$) :: V -> V -> V
($$) f a = V $ BApp $ App f a

recVal :: [(String, V)] -> V
recVal = foldr extend empty
    where
        extend (name, val) rest = V $ BRecExtend (RecExtend name val rest)
        empty = V $ BLeaf LEmptyRecord

($=) :: String -> V -> V -> V
(x $= y) z = V $ BRecExtend $ RecExtend x y z

($.) :: V -> String -> V
x $. y = V $ BGetField $ GetField x y

instance IsString V where
    fromString = V . BLeaf . LVar

data Err
    = DoesNotUnify
    | VarNotInScope String
    | OccursCheck
    | DuplicateFields [String]
    deriving (Show)

intercalate :: Doc -> [Doc] -> Doc
intercalate sep = hcat . punctuate sep

instance Pretty Err where
    pPrint DoesNotUnify = "DoesNotUnify"
    pPrint (VarNotInScope name) = text name <+> "not in scope!"
    pPrint OccursCheck = "OccursCheck"
    pPrint (DuplicateFields names) =
        "Duplicate fields in record:" <+>
        (intercalate ", " . map text) names

newtype Infer s a = Infer { unInfer :: StateT Int (EitherT Err (ST s)) a }
    deriving (Functor, Applicative, Monad)

runInfer :: (forall s. Infer s a) -> Either Err a
runInfer act = runST $ runEitherT $ (`evalStateT` 0) $ unInfer $ act

liftST :: ST s a -> Infer s a
liftST = Infer . lift . lift

throwError :: Err -> Infer s a
throwError = Infer . lift . left

data Constraints tag where
    TypeConstraints :: Constraints 'TypeT
    -- forbidden field set:
    RecordConstraints :: Set String -> Constraints 'RecordT

instance Monoid (Constraints 'TypeT) where
    mempty = TypeConstraints
    mappend _ _ = TypeConstraints

instance Monoid (Constraints 'RecordT) where
    mempty = RecordConstraints mempty
    mappend (RecordConstraints x) (RecordConstraints y) =
        RecordConstraints (x `mappend` y)

data TypeASTPosition s tag = TypeASTPosition
    { _tastPosNames :: Set (TVarName tag)
    , _tastPosType :: Either (Constraints tag) (TypeAST tag (UFTypeAST s))
    }

type UFType s = UFTypeAST s 'TypeT
type UFRecord s = UFTypeAST s 'RecordT
newtype UFTypeAST s tag = TS { tsUF :: UF s (TypeASTPosition s tag) }

type TVarBinders tag = Map (TVarName tag) (Constraints tag)

data SchemeBinders = SchemeBinders
    { schemeTypeBinders :: TVarBinders 'TypeT
    , schemeRecordBinders :: TVarBinders 'RecordT
    }
instance Monoid SchemeBinders where
    mempty = SchemeBinders Map.empty Map.empty
    mappend (SchemeBinders t0 r0) (SchemeBinders t1 r1) =
        SchemeBinders
        (Map.unionWith mappend t0 t1)
        (Map.unionWith mappend r0 r1)

data Scheme tag = Scheme
    { schemeBinders :: SchemeBinders
    , schemeType :: T tag
    }

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
    pPrint (Scheme binders typ) = pPrint binders <> "." <+> pPrint typ

data Scope s = Scope
    { _scopeLocals :: Map String (UFType s)
    , _scopeGlobals :: Map String (Scheme 'TypeT)
    }

emptyScope :: Scope s
emptyScope = Scope Map.empty Map.empty

lookupLocal :: String -> Scope s -> Maybe (UFType s)
lookupLocal str (Scope locals _) = Map.lookup str locals

lookupGlobal :: String -> Scope s -> Maybe (Scheme 'TypeT)
lookupGlobal str (Scope _ globals) = Map.lookup str globals

insertLocal :: String -> UFType s -> Scope s -> Scope s
insertLocal name typ (Scope locals globals) =
    Scope (Map.insert name typ locals) globals

freshTVarName :: Infer s (TVarName tag)
freshTVarName = modify (+1) >> get <&> TVarName & Infer

newPosition ::
    Either (Constraints tag) (TypeAST tag (UFTypeAST s)) ->
    Infer s (UFTypeAST s tag)
newPosition t =
    do
        tvarName <- freshTVarName
        TypeASTPosition (Set.singleton tvarName) t
            & liftST . UF.new <&> TS

freshTVar :: Constraints tag -> Infer s (UFTypeAST s tag)
freshTVar = newPosition . Left

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

deref :: forall s tag. IsTag tag => UFTypeAST s tag -> WriterT SchemeBinders (Infer s) (T tag)
deref ts =
    lift (getWrapper ts) >>= \(TypeASTPosition names typ) ->
    case typ of
    Left cs ->
        do
            let tvName = Set.findMin names
            tell $
                case tagRefl :: ASTTagEquality tag of
                IsTypeT Refl -> mempty { schemeTypeBinders = Map.singleton tvName cs }
                IsRecordT Refl -> mempty { schemeRecordBinders = Map.singleton tvName cs }
            return $ TVar tvName
    Right t -> t & typeSubexprs deref <&> T

generalize :: UFType s -> Infer s (Scheme 'TypeT)
generalize t =
    deref t
    & runWriterT
    <&> uncurry (flip Scheme)

unifyMatch :: v -> Lens.Getting (Monoid.First a) v a -> Infer s a
unifyMatch vTyp prism =
    case vTyp ^? prism of
    Nothing -> throwError DoesNotUnify
    Just vcontent -> return vcontent

unifyMatchEq :: Eq a => v -> a -> Lens.Getting (Monoid.First a) v a -> Infer s ()
unifyMatchEq vTyp u prism =
    do
        v <- unifyMatch vTyp prism
        unless (u == v) $ throwError DoesNotUnify

newtype PosHandler s tag = PosHandler { runPosHandler :: TypeASTPosition s tag -> Infer s () }

atAllPositions ::
    forall s tag. IsTag tag => ASTTagHandlers (PosHandler s) ->
    TypeASTPosition s tag -> Infer s ()
atAllPositions handlers =
    go
    where
        -- Let generalization is disabled because of a mountain of
        -- extensions on top
        recurse :: IsTag t => [UFTypeAST s t] -> Infer s ()
        recurse xs = mapM_ (getWrapper >=> go) xs
        recurseBoth :: ([UFTypeAST s 'TypeT], [UFTypeAST s 'RecordT]) -> Infer s ()
        recurseBoth (types, records) = recurse types >> recurse records
        go :: IsTag t => TypeASTPosition s t -> Infer s ()
        go pos@(TypeASTPosition _ mTyp) =
            do
                runPosHandler (caseTagOf handlers) pos
                mTyp & Lens.traverseOf_ Lens._Right (recurseBoth . typeSubexprsList)

occursCheck :: forall tag s. IsTag tag => Set (TVarName tag) -> TypeASTPosition s tag -> Infer s ()
occursCheck uNames pos = atAllPositions handlers pos
    where
        -- TODO: How to do this cleanly?
        handlers :: ASTTagHandlers (PosHandler s)
        handlers = ASTTagHandlers
            { atpType =
                  case tagRefl :: ASTTagEquality tag of
                  IsTypeT Refl -> PosHandler verifyNoIntersect
                  IsRecordT Refl -> PosHandler doNothing
            , atpRecord =
                  case tagRefl :: ASTTagEquality tag of
                  IsRecordT Refl -> PosHandler verifyNoIntersect
                  IsTypeT Refl -> PosHandler doNothing
            }
        doNothing _ = return ()
        verifyNoIntersect :: TypeASTPosition s tag -> Infer s ()
        verifyNoIntersect (TypeASTPosition vNames _) =
            unless (Set.null (uNames `Set.intersection`
                              vNames)) $
            throwError OccursCheck

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
    | otherwise = throwError DoesNotUnify

unifyOpenRecord :: OpenRecord s -> ClosedRecord s -> Infer s ()
unifyOpenRecord (uFields, uTail) vFields
    | Map.null uniqueUFields =
          do
              tailVal <- unflatten $ FlatRecord Nothing uniqueVFields
              unify (\_ _ -> return ()) uTail tailVal
    | otherwise = throwError DoesNotUnify
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
constraintsCheck (RecordConstraints names) r =
    do
        FlatRecord mTail fields <- flattenVal r
        let fieldsSet = Map.keysSet fields
        let forbidden = Set.intersection fieldsSet names
        unless (Set.null forbidden) $ throwError $ DuplicateFields $
            Set.toList forbidden
        case mTail of
            Nothing -> return ()
            Just rTail ->
                freshTVar (RecordConstraints fieldsSet)
                >>= unifyRecord rTail

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
        g uw@(TypeASTPosition uNames uMTyp) vw@(TypeASTPosition vNames vMTyp) =
            case (uMTyp, vMTyp) of
            (Left uCs, Left vCs) -> (Left (uCs `mappend` vCs), return ())
            (Left uCs, Right y) -> (Right y, occursCheck uNames vw >> constraintsCheck uCs y)
            (Right x, Left vCs) -> (Right x, occursCheck vNames uw >> constraintsCheck vCs x)
            (Right x, Right y) -> (Right x, f x y)
            & _1 %~ TypeASTPosition (uNames `mappend` vNames)

unifyType :: UFType s -> UFType s -> Infer s ()
unifyType =
    unify f
    where
        f (TInst uName) vTyp =
            unifyMatchEq vTyp uName _TInst
        f (TRecord uRec) vTyp =
            do
                vRec <- unifyMatch vTyp _TRecord
                unifyRecord uRec vRec
        f (TFun uArg uRes) vTyp =
            do
                (vArg, vRes) <- unifyMatch vTyp _TFun
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

inferScheme :: V -> Either Err (Scheme 'TypeT)
inferScheme x = runInfer $ infer emptyScope x >>= generalize

test :: V -> IO ()
test x =
    print $ pPrint x <+>
    case inferScheme x of
    Left err -> "causes type error:" <+> pPrint err
    Right typ -> "::" <+> pPrint typ

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

main :: IO ()
main =
    mapM_ test
    [ example1
    , example2
    , example3
    , example4
    , example5
    , example6
    ]
