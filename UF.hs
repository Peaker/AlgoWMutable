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

data GroupVal s a = GroupVal
    { groupTotal :: a
    , groupElements :: LenList (UF s a)
    }
instance Monoid a => Monoid (GroupVal s a) where
    mempty = GroupVal mempty mempty
    mappend (GroupVal t0 e0) (GroupVal t1 e1) =
        GroupVal (mappend t0 t1) (mappend e0 e1)

newtype Group s a = Group
    { groupData :: STRef s (GroupVal s a)
    } deriving (Eq)

newtype UF s a = UF
    { ufGroup :: STRef s (Group s a)
    }

new :: a -> ST s (UF s a)
new x =
    do
        group <- newSTRef (GroupVal x mempty) <&> Group
        uf <- newSTRef group <&> UF
        modifySTRef (groupData group) $
            \(GroupVal t ufs) -> GroupVal t (prepend uf ufs)
        return uf

setGroup :: Group s a -> UF s a -> ST s ()
setGroup g u = writeSTRef (ufGroup u) g

unifyGroup ::
    Monoid a => Group s a -> Group s a -> GroupVal s a -> ST s ()
unifyGroup big small smallVal =
    do
        mapM_ (setGroup big) $ lenListElems $ groupElements smallVal
        writeSTRef (groupData small) $ error "Dead group"
        modifySTRef (groupData big) $ mappend smallVal

union :: Monoid a => UF s a -> UF s a -> ST s ()
union a b =
    do
        aGroup <- readSTRef (ufGroup a)
        bGroup <- readSTRef (ufGroup b)
        aVal <- readSTRef $ groupData aGroup
        bVal <- readSTRef $ groupData bGroup
        when (aGroup /= bGroup) $
            if lenList (groupElements aVal) >= lenList (groupElements bVal)
            then unifyGroup aGroup bGroup bVal
            else unifyGroup bGroup aGroup aVal

find :: UF s a -> ST s a
find u =
    ufGroup u
    & readSTRef
    <&> groupData
    >>= readSTRef
    <&> groupTotal
