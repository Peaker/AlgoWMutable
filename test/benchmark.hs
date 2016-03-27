{-# LANGUAGE NoImplicitPrelude, OverloadedStrings #-}
import           Criterion (Benchmarkable, nf)
import           Criterion.Main (bench, defaultMain)
import           Text.PrettyPrint ((<+>))
import           Text.PrettyPrint.HughesPJClass (Pretty(..))
import qualified TestVals
import           Lamdu.Infer (inferScheme)
import           Lamdu.Expr.Val.Pure (V(..))

import           Prelude.Compat

benchInfer :: V -> Benchmarkable
benchInfer =
    nf $ \e ->
    case inferScheme TestVals.env e of
    Left err -> error $ show $ "error:" <+> pPrint err
    Right eTyped -> eTyped -- $ rnf $ eTyped ^.. folded . _1 . plType

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