{-# LANGUAGE NoImplicitPrelude, OverloadedStrings #-}
-- import Control.Exception (evaluate)
-- import Control.Lens (folded)
-- import Control.Lens.Operators
-- import Control.Lens.Tuple
-- import Control.Monad.State (evalStateT)
import           Criterion (Benchmarkable, nf)
import           Criterion.Main (bench, defaultMain)
-- import Type (infer, runInfer)
import           Text.PrettyPrint ((<+>))
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

import qualified TestVals
import           Type.Infer (inferScheme)
import           Val.Pure (V(..))

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
