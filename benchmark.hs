{-# LANGUAGE NoImplicitPrelude, OverloadedStrings #-}
import Prelude.Compat

-- import Control.Exception (evaluate)
-- import Control.Lens (folded)
-- import Control.Lens.Operators
-- import Control.Lens.Tuple
-- import Control.Monad.State (evalStateT)
import Criterion (Benchmarkable, nf)
import Criterion.Main (bench, defaultMain)
-- import Type (infer, runInfer)
import Text.PrettyPrint ((<+>))
import Text.PrettyPrint.HughesPJClass (Pretty(..))

import Type
import TestVals

benchInfer :: V -> Benchmarkable
benchInfer =
    nf $ \e ->
    case inferScheme env e of
    Left err -> error $ show $ "error:" <+> pPrint err
    Right eTyped -> eTyped -- $ rnf $ eTyped ^.. folded . _1 . plType

benches :: [(String, Benchmarkable)]
benches =
    [ ("factorial", benchInfer factorialVal)
    , ("factorialNoRecords", benchInfer factorialValNoRecords)
    -- , ("euler1", benchInfer euler1Val)
    , ("solveDepressedQuartic", benchInfer solveDepressedQuarticVal)
    -- , ("factors", benchInfer factorsVal)
    ]

main :: IO ()
main = defaultMain $ map (uncurry bench) benches
