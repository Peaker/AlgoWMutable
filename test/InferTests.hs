{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
module Main
    ( test
    , examples
    , tests, main
    ) where

import           Control.Lens.Operators
import           Lamdu.Expr.Val.Pure (V(..), ($$), (.$), ($.), ($=), ($+), ($-))
import qualified Lamdu.Expr.Val.Pure as V
import           Lamdu.Infer (inferScheme)
import           Pretty.Map ()
import           Pretty.Utils ((<+?>))
import qualified TestVals as Vals
import           Text.PrettyPrint (vcat, Doc, (<+>))
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

import           Prelude.Compat

test :: V -> Doc
test x =
    {-# SCC "test" #-}
    pPrint x <+?>
    case inferScheme Vals.env x of
    Left err -> "causes type error:" <+> pPrint err
    Right (_, typ) -> " :: " <+> pPrint typ


examples :: [V]
examples =
    [ V.lam "x" $ V.lam "y" $ V.var "x" $$ V.var "y" $$ V.var "y"
    , V.lam "x" $ V.recVal [] & "x" $= V.var "x" & "y" $= V.lambda "x" id
    , V.lam "x" $ (V.var "x" $. "y") $$ V.lambda "a" id
    , V.lam "x" $ V.var "x" $$ V.var "x"
    , V.lam "x" $ (V.var "x" $. "y") $$ (V.var "x" $. "y")
    , V.recVal [("x", V.recVal []), ("y", V.recVal [])]
    , V.lambdaRecord "params" ["x", "y", "z"] $ \[x, y, z] -> x $+ y $- z
    , V.lambda "g" $ \g ->
      V.lambda "f" $ \f ->
      V.lambda "x" $ \x ->
      g $$ (f $$ "Just" .$ x)
        $$ (f $$ "Nothing" .$ V.recVal [])
    , V.cases
      [ ("Nothing", V.lam "_" (V.litInt 0))
      , ("Just", V.lambda "x" $ \x -> V.litInt 1 $+ x)
      ]
    , V.lambda "f" $ \f ->
      V.lambda "x" $ \x ->
      (x $. "a")
      $$ (f $$ x)
      $$ (f $$ V.recVal [("a", V.hole)])
    , V.lambda "f" $ \f ->
      V.lambda "x" $ \x ->
      f $$ (x $. "a") $$ x
    , V.fromNom (fst Vals.listTypePair) $ V.lambda "x" $ \x -> x
    , V.fromNom (fst Vals.listTypePair) V.hole
    , V.fromNom (fst Vals.stTypePair) V.hole
    , V.var "runST" $$ V.hole
    , V.fromNom (fst Vals.closedStTypePair) V.hole
    , V.toNom (fst Vals.closedStTypePair) V.hole
    , V.toNom (fst Vals.closedStTypePair) (V.litInt 1)
    , V.lambda "x" $ V.toNom (fst Vals.closedStTypePair)
    ]

tests :: Doc
tests = vcat $ map test examples

main :: IO ()
main = print tests
