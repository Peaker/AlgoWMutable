{-# LANGUAGE NoImplicitPrelude, OverloadedStrings #-}
import           Control.Monad.State.Strict (evalStateT)
import           Control.Lens.Operators
import           Criterion (Benchmarkable, nf)
import           Criterion.Main (bench, defaultMain)
import           Lamdu.Expr.Val.Pure (V(..))
import qualified Lamdu.Infer as Infer
import qualified TestVals
import           Text.PrettyPrint ((<+>))
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

import           Prelude.Compat

benchInfer :: V -> Benchmarkable
benchInfer =
    nf $ \e ->
    let res =
            Infer.runInfer TestVals.env (Infer.inferScheme e)
            & (`evalStateT` Infer.emptyContext)
    in case res of
    Left err -> error $ show $ "error:" <+> pPrint err
    Right (eTyped, _zone) -> eTyped -- $ rnf $ eTyped ^.. folded . _1 . plType

benches :: [(String, Benchmarkable)]
benches =
    [ ("factorial", benchInfer TestVals.factorialVal)
    , ("factorialNoRecords", benchInfer TestVals.factorialValNoRecords)
    -- , ("euler1", benchInfer euler1Val)
    , ("solveDepressedQuartic", benchInfer TestVals.solveDepressedQuarticVal)
    -- , ("factors", benchInfer factorsVal)
    ]

main :: IO ()
main = defaultMain $ map (uncurry bench) benches
