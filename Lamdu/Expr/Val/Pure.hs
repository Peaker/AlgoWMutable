-- | Combinators to build pure Vals conveniently
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Lamdu.Expr.Val.Pure
    ( V(..)
    , lam, lambda, lambdaRecord
    , absurd, case_, cases
    , litInt, hole
    , ($$), ($$:), ($=), ($.), (.$), ($+), ($-)
    , recVal, var, infixApp
    , fromNom, toNom
    ) where

import           Lamdu.Expr.Identifier (Tag(..), NominalId)
import qualified Lamdu.Expr.Val as V
import           Pretty.Map ()
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

import           Prelude.Compat

newtype V = V (V.Val V)
    deriving (Show, Pretty)

fromNom :: NominalId -> V -> V
fromNom nomId val = V $ V.BFromNom $ V.Nom nomId val

toNom :: NominalId -> V -> V
toNom nomId val = V $ V.BToNom $ V.Nom nomId val

lam :: V.Var -> V -> V
lam name body = V $ V.BLam $ V.Abs name body

lambda :: V.Var -> (V -> V) -> V
lambda name body = lam name $ body $ var name

lambdaRecord :: V.Var -> [Tag] -> ([V] -> V) -> V
lambdaRecord name fields body = lambda name $ \v -> body $ map (v $.) fields

absurd :: V
absurd = V $ V.BLeaf V.LAbsurd

case_ :: Tag -> V -> V -> V
case_ name handler restHandlers = V $ V.BCase $ V.Case name handler restHandlers

cases :: [(Tag, V)] -> V
cases = foldr (uncurry case_) absurd

litInt :: Int -> V
litInt = V . V.BLeaf . V.LInt

hole :: V
hole = V $ V.BLeaf V.LHole

infixl 4 $$
($$) :: V -> V -> V
($$) f a = V $ V.BApp $ V.App f a

($$:) :: V -> [(Tag, V)] -> V
func $$: fields = func $$ recVal fields

recVal :: [(Tag, V)] -> V
recVal = foldr extend empty
    where
        extend (name, val) rest = V $ V.BRecExtend (V.RecExtend name val rest)
        empty = V $ V.BLeaf V.LEmptyRecord

($=) :: Tag -> V -> V -> V
(x $= y) z = V $ V.BRecExtend $ V.RecExtend x y z

($.) :: V -> Tag -> V
x $. y = V $ V.BGetField $ V.GetField x y

(.$) :: Tag -> V -> V
x .$ y = V $ V.BInject $ V.Inject x y

var :: V.Var -> V
var = V . V.BLeaf . V.LVar

infixApp :: V.Var -> V -> V -> V
infixApp name x y = var name $$: [("l", x), ("r", y)]

($+) :: V -> V -> V
($+) = infixApp "+"

($-) :: V -> V -> V
($-) = infixApp "-"
