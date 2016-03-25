{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
module InferTests
    ( test
    , example1, example2, example3, example4, example5, example6, example7, example8, example9, example10, example11
    , runTests
    ) where

import           Control.Lens.Operators
import           Data.Map (Map)
import qualified Data.Map as Map
import           Pretty.Map ()
import           Pretty.Utils ((<+?>))
import           Text.PrettyPrint (vcat, Doc, (<+>))
import           Text.PrettyPrint.HughesPJClass (Pretty(..))
import           Type.Pure (T, (~>), recordType, intType)
import           Type.Scheme (Scheme)
import qualified Type.Scheme as Scheme
import           Type.Infer (inferScheme)
import qualified Type.Infer.Scope as Scope
import           Type.Tag (ASTTag(..))
import qualified Val
import           Val.Pure (V(..), ($$), (.$), ($.), ($=), ($+), ($-))
import qualified Val.Pure as V

import           Prelude.Compat

infixType :: T 'TypeT -> T 'TypeT -> T 'TypeT -> T 'TypeT
infixType a b c = recordType [("l", a), ("r", b)] ~> c

globals :: Map Val.Var (Scheme 'TypeT)
globals =
    mconcat
    [ "+" ==> intInfix
    , "-" ==> intInfix
    ]
    where
        intInfix = Scheme.forAll 0 0 0 $ \ [] [] [] -> infixType intType intType intType
        (==>) = Map.singleton

test :: V -> Doc
test x =
    {-# SCC "test" #-}
    pPrint x <+?>
    case inferScheme (Scope.newScope globals) x of
    Left err -> "causes type error:" <+> pPrint err
    Right (_, typ) -> " :: " <+> pPrint typ


example1 :: V
example1 = V.lam "x" $ V.lam "y" $ V.var "x" $$ V.var "y" $$ V.var "y"

example2 :: V
example2 = V.lam "x" $ V.recVal [] & "x" $= V.var "x" & "y" $= V.lambda "x" id

example3 :: V
example3 = V.lam "x" $ (V.var "x" $. "y") $$ V.lambda "a" id

example4 :: V
example4 = V.lam "x" $ V.var "x" $$ V.var "x"

example5 :: V
example5 = V.lam "x" $ (V.var "x" $. "y") $$ (V.var "x" $. "y")

example6 :: V
example6 = V.recVal [("x", V.recVal []), ("y", V.recVal [])]

example7 :: V
example7 =
    V.lambdaRecord "params" ["x", "y", "z"] $ \[x, y, z] -> x $+ y $- z

example8 :: V
example8 =
    V.lambda "g" $ \g ->
    V.lambda "f" $ \f ->
    V.lambda "x" $ \x ->
    g $$ (f $$ "Just" .$ x)
      $$ (f $$ "Nothing" .$ V.recVal [])

example9 :: V
example9 =
    V.cases
    [ ("Nothing", V.lam "_" (V.litInt 0))
    , ("Just", V.lambda "x" $ \x -> V.litInt 1 $+ x)
    ]

example10 :: V
example10 =
    V.lambda "f" $ \f ->
    V.lambda "x" $ \x ->
    (x $. "a")
    $$ (f $$ x)
    $$ (f $$ V.recVal [("a", V.hole)])

example11 :: V
example11 =
    V.lambda "f" $ \f ->
    V.lambda "x" $ \x ->
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
