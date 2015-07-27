{-# LANGUAGE TemplateHaskell #-}
module UF
    ( UF
    , new, union, find
    , modify
    ) where

import           Prelude.Compat

import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.ST (ST)
import           Data.STRef

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
    { _groupTotal :: a
    , groupElements :: LenList (UF s a)
    }

newtype Group s a = Group
    { groupData :: STRef s (GroupVal s a)
    } deriving (Eq)

newtype UF s a = UF
    { ufGroup :: STRef s (Group s a)
    }

Lens.makeLenses ''GroupVal

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
    (a -> a -> (a, b)) -> Group s a -> GroupVal s a -> Group s a -> GroupVal s a -> ST s b
unifyGroup unify big (GroupVal bigTotal bigElems) small smallVal =
    do
        mapM_ (setGroup big) $ lenListElems $ groupElements smallVal
        writeSTRef (groupData small) $ error "Dead group"
        let (newTotal, res) = unify bigTotal (_groupTotal smallVal)
        writeSTRef (groupData big) $
            GroupVal newTotal $ mappend bigElems $ groupElements smallVal
        return res

union :: (a -> a -> (a, b)) -> UF s a -> UF s a -> ST s (Maybe b)
union unify a b =
    do
        aGroup <- readSTRef (ufGroup a)
        bGroup <- readSTRef (ufGroup b)
        aVal <- readSTRef $ groupData aGroup
        bVal <- readSTRef $ groupData bGroup
        if aGroup == bGroup then return Nothing
            else Just <$>
            if lenList (groupElements aVal) >= lenList (groupElements bVal)
            then unifyGroup unify aGroup aVal bGroup bVal
            else unifyGroup unify bGroup bVal aGroup aVal

find :: UF s a -> ST s a
find u =
    ufGroup u
    & readSTRef
    <&> groupData
    >>= readSTRef
    <&> _groupTotal

modify :: UF s a -> (a -> a) -> ST s ()
modify u f =
    do
        groupRef <- ufGroup u & readSTRef <&> groupData
        readSTRef groupRef
            <&> groupTotal %~ f
            >>= writeSTRef groupRef
