module UF
    ( UF
    , new, union, find
    ) where

import Control.Lens.Operators
import Control.Monad (when)
import Control.Monad.ST (ST)
import Data.STRef
import Prelude.Compat

data LenList a = LenList
    { lenList :: {-# UNPACK #-}!Int
    , lenListElems :: [a]
    }
prepend :: a -> LenList a -> LenList a
prepend x (LenList s l) = LenList (1+s) (x:l)
instance Monoid (LenList a) where
    mempty = LenList 0 []
    mappend (LenList s0 l0) (LenList s1 l1) =
        LenList (s0+s1) (l0 ++ l1)

data Group s a = Group
    { groupElements :: {-# UNPACK #-}!(STRef s (LenList (UF s a)))
    } deriving (Eq)

data UF s a = UF
    { ufData :: !a
    , ufGroup :: {-# UNPACK #-}!(STRef s (Group s a))
    }

addGroup :: Group s a -> UF s a -> ST s ()
addGroup group uf = modifySTRef (groupElements group) $ prepend uf

new :: a -> ST s (UF s a)
new x =
    do
        group <- newSTRef mempty <&> Group
        uf <- newSTRef group <&> UF x
        addGroup group uf
        return uf

setGroup :: Group s a -> UF s a -> ST s ()
setGroup g u = writeSTRef (ufGroup u) g

unifyGroup :: Group s a -> Group s a -> LenList (UF s a) -> ST s ()
unifyGroup big small smallElems =
    do
        mapM_ (setGroup big) $ lenListElems smallElems
        writeSTRef (groupElements small) $ error "Nobody should refer here!"
        modifySTRef (groupElements big) $ mappend smallElems

union :: UF s a -> UF s a -> ST s ()
union a b =
    do
        aGroup <- readSTRef (ufGroup a)
        bGroup <- readSTRef (ufGroup b)
        aElements <- readSTRef $ groupElements aGroup
        bElements <- readSTRef $ groupElements bGroup
        when (aGroup /= bGroup) $
            if lenList aElements >= lenList bElements
            then unifyGroup aGroup bGroup bElements
            else unifyGroup bGroup aGroup aElements

find :: UF s a -> ST s [a]
find u =
    ufGroup u
    & readSTRef
    <&> groupElements
    >>= readSTRef
    <&> lenListElems
    <&> map ufData
