{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
import           Data.String (IsString(..))
import           Data.Set (Set)
import           Prelude.Compat hiding (abs)

import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Lens.Tuple
import           Control.Monad (unless, (>=>))
import           Control.Monad.ST (ST, runST)
import           Control.Monad.State (StateT, evalStateT, modify, get)
import           Control.Monad.Trans.Class (lift)
import           Control.Monad.Trans.Either
import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Monoid as Monoid
import qualified Data.Set as Set
import           Text.PrettyPrint.HughesPJClass (Pretty(..), prettyParen, (<+>), (<>), text, Doc)
import           UF (UF)
import qualified UF as UF

newtype TVarName = TVarName { _tVarName :: Int }
    deriving (Eq, Ord, Show, Pretty)

data Type t
    = TFun !t !t
    | TInst String
    deriving (Show, Functor, Foldable, Traversable)

instance Pretty t => Pretty (Type t) where
    pPrintPrec level prec t =
        case t of
        TFun a b ->
            prettyParen (prec > 0) $
            pPrintPrec level 1 a <+> "->" <+> pPrintPrec level 0 b
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

data T
    = T (Type T)
    | TVar (Set TVarName)
    deriving (Show)

instance Pretty T where
    pPrintPrec level prec (T typ) = pPrintPrec level prec typ
    pPrintPrec _ _ (TVar names) = text "a" <> pPrint (Set.findMin names)

lam :: String -> V -> V
lam name body = V $ BLam $ Abs name body

infixl 4 $$
($$) :: V -> V -> V
($$) f a = V $ BApp $ App f a

instance IsString V where
    fromString = V . BLeaf . Var

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

Lens.makePrisms ''Type

data TVWrap s = TVWrap
    { tvWrapNames :: Set TVarName
    , tvWrapType :: Maybe (Type (TS s))
    }

newtype TS s = TS { tsUF :: UF s (TVWrap s) }

type Scope s = Map String (TS s)

freshTVarName :: Infer s TVarName
freshTVarName = modify (+1) >> get <&> TVarName & Infer

freshTVar :: Infer s (TS s)
freshTVar =
    freshTVarName <&> Set.singleton <&> flip TVWrap Nothing
    >>= liftST . UF.new <&> TS

wrap :: Type (TS s) -> Infer s (TS s)
wrap typ = TVWrap Set.empty (Just typ) & UF.new <&> TS & liftST

getWrapper :: TS s -> Infer s (TVWrap s)
getWrapper (TS r) = UF.find r & liftST

deref :: TS s -> Infer s T
deref ts =
    ts & getWrapper >>= \(TVWrap names typ) ->
    case typ of
    Nothing -> return $ TVar names
    Just t -> t & traverse %%~ deref <&> T

-- ref :: T -> Infer s (TS s)
-- ref = undefined

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

occursCheck :: Set TVarName -> TVWrap s -> Infer s ()
occursCheck uNames = go
    where
        go (TVWrap vNames mTyp)
            | Set.null (uNames `Set.intersection` vNames) =
                  mTyp
                  & Lens.traverseOf_ (Lens._Just . traverse)
                    (getWrapper >=> go)
            | otherwise = throwError OccursCheck

unify :: TS s -> TS s -> Infer s ()
unify u v =
    UF.union f (tsUF u) (tsUF v)
    & liftST
    >>= maybe (return ()) id
    where
        f uw@(TVWrap uNames uMTyp) vw@(TVWrap vNames vMTyp) =
            case (uMTyp, vMTyp) of
            (Nothing, Nothing) -> (Nothing, return ())
            (Nothing, Just y) -> (Just y, occursCheck uNames vw)
            (Just x, Nothing) -> (Just x, occursCheck vNames uw)
            (Just (TInst uName), Just vTyp) ->
                (uMTyp, unifyMatchEq vTyp uName _TInst)
            (Just (TFun uArg uRes), Just vTyp) ->
                ( uMTyp
                , do
                    (vArg, vRes) <- unifyMatch vTyp _TFun
                    unify uArg vArg
                    unify uRes vRes
                )
            & _1 %~ TVWrap (uNames `Set.union` vNames)

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

example :: Doc
example = test $ lam "x" $ lam "y" $ "x" $$ "y" $$ "y"
