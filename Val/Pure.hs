-- | Combinators to build pure Vals conveniently
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Val.Pure
    ( V(..)
    , lam, lambda, lambdaRecord
    , absurd, case_, cases
    , litInt, hole
    , ($$), ($$:), ($=), ($.), (.$), ($+), ($-)
    , recVal, var, global, infixApp
    ) where

import Identifier (Tag(..))
import MapPretty ()
import Text.PrettyPrint.HughesPJClass (Pretty(..))
import Val

import Prelude.Compat

newtype V = V (Val V)
    deriving (Show, Pretty)

lam :: Var -> V -> V
lam name body = V $ BLam $ Abs name body

lambda :: Var -> (V -> V) -> V
lambda name body = lam name $ body $ var name

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

infixApp :: GlobalId -> V -> V -> V
infixApp name x y = global name $$: [("l", x), ("r", y)]

($+) :: V -> V -> V
($+) = infixApp "+"

($-) :: V -> V -> V
($-) = infixApp "-"
