{-# LANGUAGE NoImplicitPrelude, OverloadedStrings #-}
import           Control.Lens.Tuple
import qualified Control.Lens as Lens
import           Control.Monad.State.Strict (evalStateT)
import           Control.Lens.Operators
import           Criterion (Benchmarkable, nf)
import           Criterion.Main (bench, defaultMain)
import           Lamdu.Expr.Val.Annotated (AV(..))
import qualified Lamdu.Infer as Infer
import qualified TestVals
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

import           Prelude.Compat

benchInfer :: AV () -> Benchmarkable
benchInfer =
    nf $ \e ->
    Infer.runInfer TestVals.env (Infer.inferScheme e)
    & (`evalStateT` Infer.emptyContext)
    & either (error . show . pPrint) (_1 . Lens.mapped %~ (^. Infer.plType) . fst)

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
