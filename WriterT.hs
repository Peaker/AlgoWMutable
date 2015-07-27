{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE BangPatterns #-}
module WriterT
    ( WriterT
    , runWriterT
    , tell
    , listen
    ) where

import Prelude.Compat

import Control.Monad.State.Strict

newtype WriterT w m a = WriterT { unWriterT :: StateT w m a }
    deriving (Functor, Applicative, Monad, MonadTrans)

runWriterT :: Monoid w => WriterT w m a -> m (a, w)
runWriterT = (`runStateT` mempty) . unWriterT

tell :: (Monoid w, Monad m) => w -> WriterT w m ()
tell !w = WriterT $ modify' (mappend w)

listenNoTell :: (Monad m, Monoid w) => WriterT w m a -> WriterT w m (a, w)
listenNoTell act = lift (runWriterT act)

listen :: (Monoid w, Monad m) => WriterT w m b -> WriterT w m b
listen act =
    do
        (res, w) <- listenNoTell act
        tell w
        return res
