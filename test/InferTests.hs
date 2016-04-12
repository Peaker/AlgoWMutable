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
import           Lamdu.Expr.Val.Annotated (AV(..), ($$), (.$), ($.), ($=), ($+), ($-))
import qualified Lamdu.Expr.Val.Annotated as AV
import           Lamdu.Infer.Deref (deref)
import qualified Lamdu.Infer.Deref as Deref
import           Lamdu.Infer (Infer)
import qualified Lamdu.Infer as Infer
import           Pretty.Map ()
import           Pretty.Utils ((<+?>))
import qualified TestVals as Vals
import           Text.PrettyPrint (vcat, Doc, (<+>), ($+$))
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

import           Prelude.Compat

type InjectPos = ALens' (AV (Infer.Payload, T 'TypeT)) (AV (Infer.Payload, T 'TypeT))

resumeTest :: AV () -> InjectPos -> AV () -> Doc
resumeTest val injectPos injectVal =
    {-# SCC "resumeTest" #-}
    case res of
    Left err -> pPrint val <+?> "causes type error:" <+> pPrint err
    Right ((av, scheme), context) ->
        vcat
        [ pPrint val <+?> " :: " <+> pPrint scheme $+$ pPrint (av <&> snd)
        , inject context av & Lens._Right %~ fst & pPrint
        ]
    where
        runInfer ::
            Infer.Context -> Infer.Scope -> (forall s. Infer s a) ->
            Either Infer.Err (a, Infer.Context)
        runInfer ctx scope act = runStateT (Infer.runInfer scope act) ctx
        inject ::
            Infer.Context -> AV (Infer.Payload, T 'TypeT) ->
            Either Infer.Err (T 'TypeT, Infer.Context)
        inject ctx av =
            runInfer ctx (ann ^. Infer.plScope) $
            do
                injectTyp <- Infer.infer injectVal <&> snd
                Infer.unifyType injectTyp $ ann ^. Infer.plType
                Deref.run $ deref injectTyp
            where
                ann = av ^# Lens.cloneLens injectPos . AV.annotation . _1
        res =
            runInfer Infer.emptyContext Vals.env $
            Infer.infer val
            <&> _1 . Lens.mapped %~ fst
            >>= _2 Deref.generalize
            >>= Deref.run . (_1 . traverse) derefDup
            where
                derefDup pl = deref (pl ^. Infer.plType) <&> (,) pl

test :: AV () -> Doc
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
            >>= _2 Deref.generalize
            >>= Deref.run . (_1 . traverse) (deref . (^. Infer.plType) . fst)

tests :: [AV ()]
tests =
    [ AV.lam "x" $ AV.lam "y" $ AV.var "x" $$ AV.var "y" $$ AV.var "y"
    , AV.lam "x" $ AV.recVal [] & "x" $= AV.var "x" & "y" $= AV.lambda "x" id
    , AV.lam "x" $ (AV.var "x" $. "y") $$ AV.lambda "a" id
    , AV.lam "x" $ AV.var "x" $$ AV.var "x"
    , AV.lam "x" $ (AV.var "x" $. "y") $$ (AV.var "x" $. "y")
    , AV.recVal [("x", AV.recVal []), ("y", AV.recVal [])]
    , AV.lambdaRecord "params" ["x", "y", "z"] $ \[x, y, z] -> x $+ y $- z
    , AV.lambda "g" $ \g ->
      AV.lambda "f" $ \f ->
      AV.lambda "x" $ \x ->
      g $$ (f $$ "Just" .$ x)
        $$ (f $$ "Nothing" .$ AV.recVal [])
    , AV.cases
      [ ("Nothing", AV.lam "_" (AV.litNum 0))
      , ("Just", AV.lambda "x" $ \x -> AV.litNum 1 $+ x)
      ]
    , AV.lambda "f" $ \f ->
      AV.lambda "x" $ \x ->
      (x $. "a")
      $$ (f $$ x)
      $$ (f $$ AV.recVal [("a", AV.hole)])
    , AV.lambda "f" $ \f ->
      AV.lambda "x" $ \x ->
      f $$ (x $. "a") $$ x
    , AV.fromNom (fst Vals.listTypePair) $ AV.lambda "x" $ \x -> x
    , AV.fromNom (fst Vals.listTypePair) AV.hole
    , AV.fromNom (fst Vals.stTypePair) AV.hole
    , AV.var "runST" $$ AV.hole
    , AV.fromNom (fst Vals.closedStTypePair) AV.hole
    , AV.toNom (fst Vals.closedStTypePair) AV.hole
    , AV.toNom (fst Vals.closedStTypePair) (AV.litNum 1)
    , AV.lambda "x" $ AV.toNom (fst Vals.closedStTypePair)
    ]

testsDoc :: Doc
testsDoc = vcat $ map test tests

resumeTests :: [(AV (), InjectPos, AV ())]
resumeTests =
    [ ( AV.lam "x" AV.hole
      , AV.val . Val._BLam . Val.lamResult & Lens.unsafeSingular
      , AV.var "x"
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
