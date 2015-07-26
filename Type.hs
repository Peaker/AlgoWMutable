{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RankNTypes #-}
module Main
    ( Infer, runInfer
    , TypeAST(..), bitraverse, typeSubexprs
    , Err(..)
    , V(..), lam, ($$), emptyRec, ($=)
    , infer
    , example, example2
    , main
    ) where

import           Prelude.Compat hiding (abs)

import           Control.Applicative (Const(..))
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
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens, (<+>), (<>), text, Doc)
import           UF (UF)
import qualified UF as UF

newtype TVarName = TVarName { _tVarName :: Int }
    deriving (Eq, Ord, Show, Pretty)

data TypeT
data RecordT
type Type = TypeAST TypeT
type Record = TypeAST RecordT

data TypeAST tag ast where
    TFun :: !(ast TypeT) -> !(ast TypeT) -> Type ast
    TInst :: String -> Type ast
    TRecord :: ast RecordT -> Type ast
    TEmptyRecord :: Record ast
    TRecExtend :: String -> ast TypeT -> ast RecordT -> Record ast

bitraverse ::
    Applicative f =>
    (ast TypeT -> f (ast' TypeT)) ->
    (ast RecordT -> f (ast' RecordT)) ->
    TypeAST tag ast -> f (TypeAST tag ast')
bitraverse typ reco = \case
    TFun a b -> TFun <$> typ a <*> typ b
    TInst n -> pure (TInst n)
    TRecord r -> TRecord <$> reco r
    TEmptyRecord -> pure TEmptyRecord
    TRecExtend n t r -> TRecExtend n <$> typ t <*> reco r

typeSubexprs ::
    Applicative f => (forall tag. ast tag -> f (ast' tag)) -> TypeAST t ast -> f (TypeAST t ast')
typeSubexprs f = bitraverse f f

typeSubexprsList :: TypeAST tag ast -> ([ast TypeT], [ast RecordT])
typeSubexprsList =
    getConst . bitraverse
    (\typ -> Const ([typ], []))
    (\reco -> Const ([], [reco]))

_TFun :: Lens.Prism' (TypeAST TypeT ast) (ast TypeT, ast TypeT)
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

_TEmptyRecord :: Lens.Prism' (Record a) ()
_TEmptyRecord = Lens.prism' (\() -> TEmptyRecord) $ \case
    TEmptyRecord -> Just ()
    _ -> Nothing

_TRecExtend :: Lens.Prism' (Record ast) (String, ast TypeT, ast RecordT)
_TRecExtend = Lens.prism' (\(n, t, r) -> TRecExtend n t r) $ \case
    TRecExtend n t r -> Just (n, t, r)
    _ -> Nothing

instance (Pretty (ast TypeT), Pretty (ast RecordT)) => Pretty (TypeAST tag ast) where
    pPrintPrec level prec ast =
        case ast of
        TFun a b ->
            maybeParens (prec > 0) $
            pPrintPrec level 1 a <+> "->" <+> pPrintPrec level 0 b
        TInst name -> "#" <> text name
        TRecord r -> pPrintPrec level prec r
        TEmptyRecord -> "{}"
        TRecExtend n t r -> "{" <+> text n <+> ":" <+> pPrint t <+> "} :" <+> pPrint r

data Leaf
    = LVar String
    | LEmptyRecord
    deriving (Show)

data Abs v = Abs String !v
    deriving (Show, Functor, Foldable, Traversable)

data App v = App !v !v
    deriving (Show, Functor, Foldable, Traversable)

data RecExtend v = RecExtend String !v !v
    deriving (Show, Functor, Foldable, Traversable)

data Val v
    = BLam (Abs v)
    | BApp (App v)
    | BRecExtend (RecExtend v)
    | BLeaf Leaf
    deriving (Show, Functor, Foldable, Traversable)

newtype V = V (Val V)
    deriving (Show)

data T tag
    = T (TypeAST tag T)
    | TVar (Set TVarName)

instance Pretty (T tag) where
    pPrintPrec level prec (T typ) = pPrintPrec level prec typ
    pPrintPrec _ _ (TVar names) = text "a" <> pPrint (Set.findMin names)

lam :: String -> V -> V
lam name body = V $ BLam $ Abs name body

infixl 4 $$
($$) :: V -> V -> V
($$) f a = V $ BApp $ App f a

emptyRec :: V
emptyRec = V $ BLeaf LEmptyRecord

($=) :: String -> V -> V -> V
(x $= y) z = V $ BRecExtend $ RecExtend x y z

instance IsString V where
    fromString = V . BLeaf . LVar

data Err
    = DoesNotUnify
    | VarNotInScope String
    | OccursCheck
    deriving (Show)

instance Pretty Err where
    pPrint DoesNotUnify = "DoesNotUnify"
    pPrint (VarNotInScope name) = text name <+> "not in scope!"
    pPrint OccursCheck = "OccursCheck"

newtype Infer s a = Infer { unInfer :: StateT Int (EitherT Err (ST s)) a }
    deriving (Functor, Applicative, Monad)

runInfer :: (forall s. Infer s a) -> Either Err a
runInfer act = runST $ runEitherT $ (`evalStateT` 0) $ unInfer $ act

liftST :: ST s a -> Infer s a
liftST = Infer . lift . lift

throwError :: Err -> Infer s a
throwError = Infer . lift . left

data TypeASTPosition s tag = TypeASTPosition
    { _tvWrapNames :: Set TVarName
    , _tvWrapType :: Maybe (TypeAST tag (UFTypeAST s))
    }

type UFType s = UFTypeAST s TypeT
type UFRecord s = UFTypeAST s RecordT
newtype UFTypeAST s tag = TS { tsUF :: UF s (TypeASTPosition s tag) }

type Scope s = Map String (UFType s)

freshTVarName :: Infer s TVarName
freshTVarName = modify (+1) >> get <&> TVarName & Infer

freshTVar :: Infer s (UFTypeAST s tag)
freshTVar =
    freshTVarName <&> Set.singleton <&> flip TypeASTPosition Nothing
    >>= liftST . UF.new <&> TS

wrap :: TypeAST tag (UFTypeAST s) -> Infer s (UFTypeAST s tag)
wrap typ = TypeASTPosition Set.empty (Just typ) & UF.new <&> TS & liftST

getWrapper :: UFTypeAST s tag -> Infer s (TypeASTPosition s tag)
getWrapper (TS r) = UF.find r & liftST

deref :: UFTypeAST s tag -> Infer s (T tag)
deref ts =
    ts & getWrapper >>= \(TypeASTPosition names typ) ->
    case typ of
    Nothing -> return $ TVar names
    Just t -> t & typeSubexprs deref <&> T

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

occursCheck :: Set TVarName -> TypeASTPosition s tag -> Infer s ()
occursCheck uNames = go
    where
        recurse xs = mapM_ (getWrapper >=> go) xs
        -- TODO: Why is a typesig needed here?
        recurseBoth :: ([UFType s], [UFRecord s]) -> Infer s ()
        recurseBoth (types, records) = recurse types >> recurse records
        -- TODO: Why is a typesig needed here?
        go :: TypeASTPosition s tag -> Infer s ()
        go (TypeASTPosition vNames mTyp)
            | Set.null (uNames `Set.intersection` vNames) =
                  mTyp
                  & Lens.traverseOf_ Lens._Just (recurseBoth . typeSubexprsList)
            | otherwise = throwError OccursCheck

type RecordTail s = (Set TVarName, UFRecord s)
type RecordFields s = Map String (UFType s)
type ClosedRecord s = RecordFields s
type OpenRecord s = (RecordFields s, RecordTail s)

data FlatRecord s = FlatRecord
    { __frMTail :: Maybe (RecordTail s)
    , _frFields :: RecordFields s
    }

Lens.makeLenses ''FlatRecord

flatten :: UFRecord s -> Infer s (FlatRecord s)
flatten ts =
    do
        TypeASTPosition names typ <- getWrapper ts
        case typ of
            Nothing -> return $ FlatRecord (Just (names, ts)) Map.empty
            Just TEmptyRecord -> return $ FlatRecord Nothing Map.empty
            Just (TRecExtend n t r) ->
                flatten r <&> frFields . Lens.at n ?~ t

unflatten :: FlatRecord s -> Infer s (UFRecord s)
unflatten (FlatRecord mTail fields) =
    Map.toList fields & go
    where
        go [] =
            case mTail of
            Nothing -> wrap TEmptyRecord
            Just (_, tailVal) -> return tailVal
        go ((name, typ):fs) =
            go fs
            <&> TRecExtend name typ
            >>= wrap

unifyClosedRecords :: ClosedRecord s -> ClosedRecord s -> Infer s ()
unifyClosedRecords uFields vFields
    | Map.keysSet uFields == Map.keysSet vFields =
          Map.intersectionWith unifyType uFields vFields
          & sequenceA_
    | otherwise = throwError DoesNotUnify

unifyOpenRecord :: OpenRecord s -> ClosedRecord s -> Infer s ()
unifyOpenRecord (uFields, (_, uTail)) vFields
    | Map.null uniqueUFields =
          do
              tailVal <- unflatten $ FlatRecord Nothing uniqueVFields
              unify (\_ _ -> return ()) uTail tailVal
    | otherwise = throwError DoesNotUnify
    where
        uniqueUFields = uFields `Map.difference` vFields
        uniqueVFields = vFields `Map.difference` uFields

unifyOpenRecords :: OpenRecord s -> OpenRecord s -> Infer s ()
unifyOpenRecords = undefined

unifyRecord :: UFRecord s -> UFRecord s -> Infer s ()
unifyRecord u v =
    do
        FlatRecord uMTail uFields <- flatten u
        FlatRecord vMTail vFields <- flatten v
        case (uMTail, vMTail) of
            (Nothing, Nothing) -> unifyClosedRecords uFields vFields
            (Just uTail, Nothing) -> unifyOpenRecord (uFields, uTail) vFields
            (Nothing, Just vTail) -> unifyOpenRecord (vFields, vTail) uFields
            (Just uTail, Just vTail) -> unifyOpenRecords (uFields, uTail) (vFields, vTail)

unify ::
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
            (Nothing, Nothing) -> (Nothing, return ())
            (Nothing, Just y) -> (Just y, occursCheck uNames vw)
            (Just x, Nothing) -> (Just x, occursCheck vNames uw)
            (Just x, Just y) -> (Just x, f x y)
            & _1 %~ TypeASTPosition (uNames `Set.union` vNames)

unifyType :: UFType s -> UFType s -> Infer s ()
unifyType u v =
    unify f u v
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
    LVar n ->
        case Map.lookup n scope of
        Just typ -> return typ
        Nothing -> throwError $ VarNotInScope n

inferLam :: Scope s -> Abs V -> Infer s (UFType s)
inferLam scope (Abs n body) =
    do
        nType <- freshTVar
        resType <- infer (Map.insert n nType scope) body
        TFun nType resType & wrap

inferApp :: Scope s -> App V -> Infer s (UFType s)
inferApp scope (App fun arg) =
    do
        funTyp <- infer scope fun
        argTyp <- infer scope arg
        resTyp <- freshTVar

        expectedFunTyp <- TFun argTyp resTyp & wrap
        unifyType expectedFunTyp funTyp
        return resTyp

inferRecExtend :: Scope s -> RecExtend V -> Infer s (UFType s)
inferRecExtend scope (RecExtend name val rest) =
    do
        valTyp <- infer scope val
        restTyp <- infer scope rest
        unknownRestFields <- freshTVar
        expectedResTyp <- TRecord unknownRestFields & wrap
        unifyType expectedResTyp restTyp
        TRecExtend name valTyp unknownRestFields
            & wrap
            >>= wrap . TRecord

infer :: Scope s -> V -> Infer s (UFType s)
infer scope (V v) =
    case v of
    BLeaf l -> inferLeaf scope l
    BLam abs -> inferLam scope abs
    BApp app -> inferApp scope app
    BRecExtend ext -> inferRecExtend scope ext

test :: V -> Doc
test x = pPrint $ runInfer $ infer mempty x >>= deref

example :: Doc
example = test $ lam "x" $ lam "y" $ "x" $$ "y" $$ "y"

example2 :: Doc
example2 =
    test $ lam "x" $
    emptyRec
    & "x" $= "x"
    & "y" $= lam "x" "x"

main :: IO ()
main = mapM_ print [example, example2]
