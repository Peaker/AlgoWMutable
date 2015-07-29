{-# LANGUAGE NoImplicitPrelude #-}
module TestRefZone where

import Control.Monad
import Control.Monad.ST
import Prelude.Compat
import RefZone

main :: IO ()
main = print ok
    where
        (frozen, ref) =
            freeze $
            do
                zone <- new
                r <- newRef zone "Hi"
                writeRef zone r "Hi"
                return (zone, r)
        ref' = runST $
             do
                 zone0 <- clone frozen
                 zone1 <- clone frozen
                 o0 <- readRef zone0 ref
                 o1 <- readRef zone1 ref
                 when ((o0, o1) /= ("Hi", "Hi")) $ error ("BUG1: " ++ show (o0, o1))
                 writeRef zone0 ref "Hi0"
                 o0' <- readRef zone0 ref
                 o1' <- readRef zone1 ref
                 when ((o0', o1') /= ("Hi0", "Hi")) $ error ("BUG2: " ++ show (o0', o1'))
                 ref0 <- newRef zone0 "Z0"
                 ref1 <- newRef zone1 "Z1"
                 z0 <- readRef zone0 ref0
                 z1 <- readRef zone1 ref1
                 when ((z0, z1) /= ("Z0", "Z1")) $ error ("BUG3: " ++ show (z0, z1))
                 return ref
        ok = runST $
             do
                 zone0 <- clone frozen
                 o <- readRef zone0 ref'
                 when (o /= "Hi") $ error ("BUG4: " ++ show o)
                 return "OK"
