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
import           Control.Monad.State.Strict (StateT(..), evalStateT, mapStateT)
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
import           Text.PrettyPrint (vcat, Doc, (<>), (<+>), ($+$), text)
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

import           Prelude.Compat hiding ((<>))

type InjectPos = ALens' (AV Infer.Payload) (AV Infer.Payload)

data ResumptionErr = InferErr Int | DerefErr Int | UnifyInjectErr Int
    deriving (Eq, Ord, Show)
instance Pretty ResumptionErr where pPrint = text . show

annotateErr :: ann -> StateT s (Either e) a -> StateT s (Either (ann, e)) a
annotateErr ann = mapStateT (Lens._Left %~ (,) ann)

type Resumption = (InjectPos, AV ())
type ResumeTest = (AV (), [Resumption])

resumeTest :: ResumeTest -> Doc
resumeTest (val, resumptions) =
    {-# SCC "resumeTest" #-}
    do
        (av, topTyp) <-
            runInfer (InferErr 0, pPrint val) $
            Infer.infer val Vals.env <&> _1 . Lens.mapped %~ fst
        topScheme <-
            runInfer (DerefErr 0, pPrint topTyp) $ Deref.run $ Deref.generalize topTyp
        let topLevelDoc =
                pPrint val <+?> "::" <+> pPrint topScheme
                $+$ pPrint (av <&> (^. Infer.plType))
        docs <- zip [1..] resumptions & traverse (resume av topTyp)
        vcat (topLevelDoc : docs) & return
    & (`evalStateT` Infer.emptyContext)
    & either pPrintErr id
    where
        resume av topTyp (i, (injectPos, injectVal)) =
            do
                injectTyp <-
                    runInfer (InferErr i, pPrint injectVal) $ Infer.infer injectVal posScope <&> snd
                runInfer (UnifyInjectErr i, pPrint injectTyp <+> pPrint posTyp) $
                    Infer.unifyType injectTyp posTyp
                (injectTypD, topScheme) <-
                    runInfer (DerefErr i, pPrint injectTyp <+> "," <+> pPrint topTyp) $
                    Deref.run $ (,) <$> Deref.deref injectTyp <*> Deref.generalize topTyp
                pPrint injectVal <+> "::" <+> pPrint injectTypD
                    $+$ "top-level becomes: " <> pPrint topScheme
                    & return
            where
                Infer.Payload posTyp posScope =
                    av ^# Lens.cloneLens injectPos . AV.annotation
        pPrintErr ((resErr, doc), inferErr) =
            pPrint resErr <> ":" <+> doc <> ":" <+> pPrint inferErr
        runInfer ::
            ann -> (forall s. Infer s a) ->
            StateT Infer.Context (Either (ann, Infer.Err)) a
        runInfer errAnn act = annotateErr errAnn $ Infer.runInfer act

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
            Infer.runInfer $
            Infer.infer x Vals.env
            & Deref.liftInfer
            >>= _2 Deref.generalize
            >>= (_1 . traverse) (deref . (^. Infer.plType) . fst)
            & Deref.run

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

lamRes :: Lens.Traversal' (AV a) (AV a)
lamRes = AV.val . Val._BLam . Val.lamResult

appArg :: Lens.Traversal' (AV a) (AV a)
appArg = AV.val . Val._BApp . Val.applyArg

appFunc :: Lens.Traversal' (AV a) (AV a)
appFunc = AV.val . Val._BApp . Val.applyFunc

resumeTests :: [ResumeTest]
resumeTests =
    [ ( AV.lam "x" AV.hole
      , [ (lamRes & Lens.unsafeSingular, AV.var "x")
        ]
      )
    , let inLambdas = lamRes . lamRes . lamRes . lamRes
      in
      ( AV.lambda "f" $ \f ->
        AV.lambda "g" $ \g ->
        AV.lambda "a" $ \a ->
        AV.lambda "b" $ \_b ->
        f $$ (g $$ a $$ a) $$ (g $$ AV.hole $$ AV.hole)
      , [ ( inLambdas . appArg . appArg & Lens.unsafeSingular
          , AV.litNum 1
          )
        , ( inLambdas . appArg . appFunc . appArg & Lens.unsafeSingular
          , AV.var "b"
          )
        ]
      )
    ]

resumeTestsDoc :: Doc
resumeTestsDoc = vcat $ map resumeTest resumeTests

main :: IO ()
main =
    do
        -- print resumption
        print testsDoc
        print resumeTestsDoc
