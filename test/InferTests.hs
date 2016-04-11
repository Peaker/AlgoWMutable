{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
module Main
    ( test, resumeTest
    , tests, resumeTests
    , main
    ) where

import           Control.Lens (ALens')
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Lens.Tuple
import           Control.Monad.State.Strict (StateT(..), evalStateT)
import           Lamdu.Expr.Type.Pure (T)
import           Lamdu.Expr.Type.Tag (ASTTag(..))
import qualified Lamdu.Expr.Val as Val
import           Lamdu.Expr.Val.Annotated (AV)
import qualified Lamdu.Expr.Val.Annotated as AV
import           Lamdu.Expr.Val.Pure (V(..), ($$), (.$), ($.), ($=), ($+), ($-))
import qualified Lamdu.Expr.Val.Pure as V
import           Lamdu.Infer (Infer, MetaType)
import qualified Lamdu.Infer as Infer
import           Pretty.Map ()
import           Pretty.Utils ((<+?>))
import qualified TestVals as Vals
import           Text.PrettyPrint (vcat, Doc, (<+>), ($+$))
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

import           Prelude.Compat

type InjectPos = ALens' (AV (MetaType, T 'TypeT)) (AV (MetaType, T 'TypeT))

resumeTest :: V -> InjectPos -> V -> Doc
resumeTest val injectPos injectVal =
    {-# SCC "resumeTest" #-}
    case res of
    Left err -> pPrint val <+?> "causes type error:" <+> pPrint err
    Right ((av, scheme), newContext) ->
        vcat
        [ pPrint val <+?> " :: " <+> pPrint scheme $+$ pPrint (av <&> snd)
        , let eInjectedTyp = Lens._Right %~ fst $ runInfer newContext $ inject av
          in  pPrint eInjectedTyp
        ]
    where
        runInfer ::
            Infer.Context -> (forall s. Infer s a) ->
            Either Infer.Err (a, Infer.Context)
        runInfer ctx act = runStateT (Infer.runInfer Vals.env act) ctx
        inject :: AV (MetaType, T 'TypeT) -> Infer s (T 'TypeT)
        inject av =
            do
                injectTyp <- Infer.infer injectVal <&> snd
                Infer.unifyType injectTyp $ av ^# Lens.cloneLens injectPos . AV.annotation . _1
                Infer.runDeref $ Infer.deref injectTyp
        res =
            runInfer Infer.emptyContext $
            Infer.infer val
            >>= _2 Infer.generalize
            >>= Infer.runDeref . _1 (traverse derefDup)
            where
                derefDup x = Infer.deref x <&> (,) x

test :: V -> Doc
test x =
    {-# SCC "test" #-}
    pPrint x <+?>
    case res of
    Left err -> "causes type error:" <+> pPrint err
    Right (av, scheme) -> " :: " <+> pPrint scheme $+$ pPrint av
    where
        res =
            (`evalStateT` Infer.emptyContext) $
            Infer.runInfer Vals.env $
            Infer.infer x
            >>= _2 Infer.generalize
            >>= Infer.runDeref . _1 (traverse Infer.deref)

tests :: [V]
tests =
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

testsDoc :: Doc
testsDoc = vcat $ map test tests

resumeTests :: [(V, InjectPos, V)]
resumeTests =
    [ ( V.lam "x" V.hole
      , AV.val . Val._BLam . Val.lamResult & Lens.unsafeSingular
      , V.var "x"
      )
    ]

resumeTestsDoc :: Doc
resumeTestsDoc =
    vcat $ map f resumeTests
    where
        f (val, injectPos, injectVal) = resumeTest val injectPos injectVal

main :: IO ()
main =
    do
        -- print resumption
        print testsDoc
        print resumeTestsDoc
