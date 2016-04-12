{-# LANGUAGE RankNTypes, NoImplicitPrelude, GeneralizedNewtypeDeriving #-}
module Data.RefZone
    ( Zone, new
    , Frozen, freeze, clone, emptyFrozen
    , Ref, newRef, readRef, writeRef, modifyRef
    ) where

import           Control.DeepSeq (NFData(..))
import           Control.Lens.Operators
import           Control.Monad.ST (ST, runST)
import           Data.RefZone.Internal
import           Data.STRef
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import           Unsafe.Coerce

import           Prelude.Compat

data Box

unsafeFromBox :: Box -> a
unsafeFromBox = unsafeCoerce

toBox :: a -> Box
toBox = unsafeCoerce

data Zone s = Zone
    { _zoneSizeRef  :: {-# UNPACK #-}!(STRef s Int) -- vector grows beyond this
    , zoneVectorRef :: {-# UNPACK #-}!(STRef s (MV.STVector s Box))
    }
instance NFData (Zone s) where rnf (Zone s v) = s `seq` v `seq` ()

newtype Frozen = Frozen (V.Vector Box)

emptyFrozen :: Frozen
emptyFrozen = Frozen mempty

{-# INLINE initialSize #-}
initialSize :: Int
initialSize = 256
{-# INLINE growthFactor #-}
growthFactor :: Int
growthFactor = 2

new :: ST s (Zone s)
new = Zone <$> newSTRef 0 <*> (MV.new initialSize >>= newSTRef)

freeze :: Traversable t => (forall s. ST s (t (Zone s))) -> t Frozen
freeze action =
    runST $ action >>= traverse onZone
    where
        onZone (Zone sizeRef mvectorRef) =
            do
                size <- readSTRef sizeRef
                vector <- readSTRef mvectorRef >>= V.unsafeFreeze <&> V.slice 0 size
                Frozen vector & return

clone :: Frozen -> ST s (Zone s)
clone (Frozen vector) =
    do
        mvector <- MV.new (max (V.length vector) initialSize)
        V.copy (MV.slice 0 len mvector) vector
        Zone <$> newSTRef len <*> newSTRef mvector
    where
        len = V.length vector

{-# INLINE incSize #-}
incSize :: Zone s -> ST s (MV.STVector s Box, Int)
incSize (Zone sizeRef mvectorRef) =
    do
        size <- readSTRef sizeRef
        mvector <- readSTRef mvectorRef
        let len = MV.length mvector
        incSizeH size =<<
            if size == len
            then
            do
                grownMvector <- MV.new (growthFactor * len)
                MV.copy (MV.slice 0 len grownMvector) mvector
                writeSTRef mvectorRef grownMvector
                return grownMvector
            else
                return mvector
    where
        -- This is separated to avoid shadowing and/or having a stale mvector in scope
        incSizeH size mvector =
            do
                writeSTRef sizeRef (size + 1)
                return (mvector, size)

{-# INLINE newRef #-}
newRef :: Zone s -> a -> ST s (Ref a)
newRef zone val =
    do
        (mvector, size) <- incSize zone
        val & toBox & MV.unsafeWrite mvector size
        Ref size & return

{-# INLINE readRef #-}
readRef :: Zone s -> Ref a -> ST s a
readRef zone (Ref i) =
    readSTRef (zoneVectorRef zone) >>= (MV.unsafeRead ?? i) <&> unsafeFromBox

{-# INLINE writeRef #-}
writeRef :: Zone s -> Ref a -> a -> ST s ()
writeRef zone (Ref i) val =
    do
        mvector <- readSTRef (zoneVectorRef zone)
        toBox val & MV.unsafeWrite mvector i

{-# INLINE modifyRef #-}
modifyRef :: Zone s -> Ref a -> (a -> a) -> ST s ()
modifyRef zone (Ref i) f =
    do
        mvector <- readSTRef (zoneVectorRef zone)
        MV.unsafeRead mvector i
            <&> unsafeFromBox
            <&> f
            <&> toBox
            >>= MV.unsafeWrite mvector i
