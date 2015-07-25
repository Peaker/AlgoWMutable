{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
import           Prelude.Compat hiding (abs)

import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad
import           Control.Monad.ST (ST, runST)
import           Control.Monad.State
import           Control.Monad.Trans.Either
import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Monoid as Monoid
import           Data.STRef
import           Text.PrettyPrint.HughesPJClass

newtype TVarName = TVarName { _tVarName :: Int }
    deriving (Eq, Show, Pretty)

Lens.makeLenses ''TVarName

data Type t
    = TFun !t !t
    | TInst String
    | TVar {-# UNPACK #-}!TVarName
    deriving (Show, Functor, Foldable, Traversable)

instance Pretty t => Pretty (Type t) where
    pPrintPrec level prec t =
        case t of
        TFun a b ->
            prettyParen (prec > 0) $
            pPrintPrec level 1 a <+> "->" <+> pPrintPrec level 0 b
        TVar name -> "a" <> pPrint name
        TInst name -> "#" <> text name

data Leaf
    = Var String
    deriving (Show)

data Abs v = Abs String !v
    deriving (Show, Functor, Foldable, Traversable)

data App v = App !v !v
    deriving (Show, Functor, Foldable, Traversable)

data Val v
    = BLam (Abs v)
    | BApp (App v)
    | BLeaf Leaf
    deriving (Show, Functor, Foldable, Traversable)

newtype V = V (Val V)
    deriving (Show)

newtype T = T (Type T)
    deriving (Show, Pretty)

lam :: String -> V -> V
lam name body = V $ BLam $ Abs name body

apply :: V -> V -> V
apply f a = V $ BApp $ App f a

var :: String -> V
var = V . BLeaf . Var

newtype Context = Context
    { _cFresh :: TVarName
    } deriving (Show, Pretty)

data Err
    = DoesNotUnify
    | VarNotInScope String
    deriving (Show)

instance Pretty Err where
    pPrint DoesNotUnify = "DoesNotUnify"
    pPrint (VarNotInScope name) = text name <+> "not in scope!"

newtype Infer s a = Infer { unInfer :: StateT Context (EitherT Err (ST s)) a }
    deriving (Functor, Applicative, Monad)

runInfer :: (forall s. Infer s a) -> Either Err a
runInfer act = runST $ runEitherT $ (`evalStateT` Context (TVarName 0)) $ unInfer $ act

liftST :: ST s a -> Infer s a
liftST = Infer . lift . lift

throwError :: Err -> Infer s a
throwError = Infer . lift . left

Lens.makeLenses ''Context
Lens.makePrisms ''Type

newtype TS s = TS (STRef s (Type (TS s)))

type Scope s = Map String (TS s)

wrap :: Type (TS s) -> Infer s (TS s)
wrap typ = newSTRef typ <&> TS & liftST

unwrap :: TS s -> Infer s (Type (TS s))
unwrap (TS r) = readSTRef r & liftST

deref :: TS s -> Infer s T
deref ts = ts & unwrap >>= traverse %%~ deref <&> T

ref :: T -> Infer s (TS s)
ref = undefined

freshTVarName :: Infer s TVarName
freshTVarName =
    Infer $
    do
        cFresh . tVarName += 1
        Lens.use cFresh

freshTVar :: Infer s (TS s)
freshTVar = freshTVarName <&> TVar >>= wrap

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

varBind :: TVarName -> Type t -> Infer s ()
varBind name typ =
    unifyMatchEq typ name _TVar

unify :: TS s -> TS s -> Infer s ()
unify u v =
    do
        uTyp <- unwrap u
        vTyp <- unwrap v
        let getV = unifyMatch vTyp
        case (uTyp, vTyp) of
            (TVar uName, _) -> varBind uName vTyp
            (_, TVar vName) -> varBind vName uTyp
            (TInst uName, _) ->
                do
                    vName <- getV _TInst
                    unless (uName == vName) $ throwError $ DoesNotUnify
            (TFun uArg uRes, _) ->
                do
                    (vArg, vRes) <- getV _TFun
                    unify uArg vArg
                    unify uRes vRes

inferLeaf :: Map String a -> Leaf -> Infer s a
inferLeaf scope leaf =
    case leaf of
    Var n ->
        case Map.lookup n scope of
        Just typ -> return typ
        Nothing -> throwError $ VarNotInScope n

inferLam :: Map String (TS s) -> Abs V -> Infer s (TS s)
inferLam scope (Abs n body) =
    do
        nType <- freshTVar
        resType <- infer (Map.insert n nType scope) body
        TFun nType resType & wrap

inferApp :: Scope s -> App V -> Infer s (TS s)
inferApp scope (App fun arg) =
    do
        funTyp <- infer scope fun
        argTyp <- infer scope arg
        resTyp <- freshTVar

        expectedFunTyp <- TFun argTyp resTyp & wrap
        unify expectedFunTyp funTyp
        return resTyp

infer :: Scope s -> V -> Infer s (TS s)
infer scope (V v) =
    case v of
    BLeaf l -> inferLeaf scope l
    BLam abs -> inferLam scope abs
    BApp app -> inferApp scope app

test :: V -> Doc
test x = pPrint $ runInfer $ infer mempty x >>= deref
