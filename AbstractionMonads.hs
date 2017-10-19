{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module AbstractionMonads where

import Control.Monad.State
import Control.Applicative
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Writer
import Data.Functor.Identity

----------------------------------------
-- Store Monad
----------------------------------------

newtype StateTStore s m a = StateTStore (StateT s m a)
  deriving (Functor, Applicative, Monad, MonadTrans, MonadFix,
            MonadPlus, Alternative, MonadIO,
            MonadReader r, MonadError e, MonadWriter w)

evalStateTStore (StateTStore m) s = evalStateT m s
evalStateStore  (StateTStore m) s  = evalState  m s

runStateTStore (StateTStore m) s = runStateT m s
runStateStore  (StateTStore m) s = runState  m s

class Monad m => MonadStateStore s m | m -> s where
  getStore :: m s
  putStore :: s -> m ()
  updateStore :: (s -> s) -> m ()

instance Monad m => MonadStateStore s (StateTStore s m) where
  getStore = StateTStore get
  putStore s = StateTStore (put s)
  updateStore f = StateTStore (modify f)

instance MonadStateStore s m => MonadStateStore s (ReaderT e m) where
  getStore = ReaderT (\_ -> getStore)
  putStore s = ReaderT (\_ -> putStore s)
  updateStore f = ReaderT (\_ -> updateStore f)

instance MonadStateStore s m => MonadStateStore s (ExceptT e m) where
  getStore = lift getStore
  putStore = lift . putStore
  updateStore = lift . updateStore

----------------------------------------
-- StateTDead
----------------------------------------

newtype StateTDead s m a = StateTDead (StateT s m a)
  deriving (Functor, Applicative, Monad, MonadTrans, MonadFix,
            MonadPlus, Alternative, MonadIO,
            MonadReader r, MonadError e, MonadWriter w)

runStateTDead :: StateTDead s m a -> s -> m (a, s)
runStateTDead (StateTDead m) s = runStateT m s

mkStateTDead m = StateTDead (StateT m)

class Monad m => MonadStateDead s m | m -> s where
  getDead :: m s
  putDead :: s -> m ()
  updateDead :: (s -> s) -> m ()

instance Monad m => MonadStateDead s (StateTDead s m) where
  getDead = StateTDead get
  putDead s = StateTDead (put s)
  updateDead f = StateTDead (modify f)

instance MonadStateDead s m => MonadStateDead s (ReaderT e m) where
  getDead = ReaderT (\_ -> getDead)
  putDead s = ReaderT (\_ -> putDead s)
  updateDead f = ReaderT (\_ -> updateDead f)

instance MonadStateDead s m => MonadStateDead s (ExceptT e m) where
  getDead = lift getDead
  putDead = lift . putDead
  updateDead = lift . updateDead

instance MonadStateDead s m => MonadStateDead s (StateTStore s' m) where
  getDead = lift getDead
  putDead = lift . putDead
  updateDead = lift . updateDead

----------------------------------------
-- StateTCacheOut
----------------------------------------

newtype StateTCacheOut s m a = StateTCacheOut (StateT s m a)
  deriving (Functor, Applicative, Monad, MonadTrans, MonadFix,
            MonadPlus, Alternative, MonadIO,
            MonadReader r, MonadError e, MonadWriter w)

runStateTCacheOut :: StateTCacheOut s m a -> s -> m (a, s)
runStateTCacheOut (StateTCacheOut m) s = runStateT m s

mkStateTCacheOut m = StateTCacheOut (StateT m)

class Monad m => MonadStateCacheOut s m | m -> s where
  getCacheOut :: m s
  putCacheOut :: s -> m ()
  updateCacheOut :: (s -> s) -> m ()

instance Monad m => MonadStateCacheOut s (StateTCacheOut s m) where
  getCacheOut = StateTCacheOut get
  putCacheOut s = StateTCacheOut (put s)
  updateCacheOut f = StateTCacheOut (modify f)

instance MonadStateCacheOut s m => MonadStateCacheOut s (ReaderT e m) where
  getCacheOut = ReaderT (\_ -> getCacheOut)
  putCacheOut s = ReaderT (\_ -> putCacheOut s)
  updateCacheOut f = ReaderT (\_ -> updateCacheOut f)

instance MonadStateCacheOut s m => MonadStateCacheOut s (ExceptT e m) where
  getCacheOut = lift getCacheOut
  putCacheOut = lift . putCacheOut
  updateCacheOut = lift . updateCacheOut

instance MonadStateCacheOut s m => MonadStateCacheOut s (StateTStore s' m) where
  getCacheOut = lift getCacheOut
  putCacheOut = lift . putCacheOut
  updateCacheOut = lift . updateCacheOut

----------------------------------------
-- Nondeterminism monad
----------------------------------------

newtype ND m a =
  ND { unND :: forall r. (a -> m r -> m r) -> m r -> m r }

runND :: ND Identity a -> [a]
runND (ND f) = runIdentity $
  f (\a (Identity as) -> Identity (a:as)) (Identity [])

instance Monad (ND m) where
  return a = ND (\k -> k a)
  ND f >>= g = ND (\k -> f (\a -> unND (g a) k))

instance Applicative (ND m) where
  pure = return
  (<*>) = ap

instance Functor (ND m) where
  fmap f (ND g) = ND (\k -> g (\a -> k (f a)))

instance MonadPlus (ND m) where
  mzero = ND (\sk fk -> fk)
  ND f `mplus` ND g = ND (\sk fk -> f (\a fk' -> sk a fk')
                                      (g (\a fk' -> sk a fk') fk))

instance Alternative (ND m) where
  empty = mzero
  (<|>) = mplus

----------------------------------------
-- Specialized reader monad
----------------------------------------
-- Currently not used.

newtype ReaderTEnv r m a = ReaderTEnv (ReaderT r m a)
  deriving (Functor, Applicative, Monad, MonadTrans, MonadFix,
            MonadPlus, Alternative, MonadIO,
            MonadState s, MonadError e, MonadWriter w)

class Monad m => MonadReaderEnv e m | m -> e where
  askEnv   :: m e
  localEnv :: (e -> e) -> m a -> m a

instance Monad m => MonadReaderEnv e (ReaderTEnv e m) where
  askEnv = ReaderTEnv ask
  localEnv f (ReaderTEnv r) = ReaderTEnv (local f r)

----------------------------------------
-- Cache in reader monad
----------------------------------------

newtype ReaderTCacheIn r m a = ReaderTCacheIn (ReaderT r m a)
  deriving (Functor, Applicative, Monad, MonadTrans, MonadFix,
            MonadPlus, Alternative, MonadIO,
            MonadState s, MonadError e, MonadWriter w)

class Monad m => MonadReaderCacheIn e m | m -> e where
  askCacheIn   :: m e
  localCacheIn :: (e -> e) -> m a -> m a

instance Monad m => MonadReaderCacheIn e (ReaderTCacheIn e m) where
  askCacheIn = ReaderTCacheIn ask
  localCacheIn f (ReaderTCacheIn r) = ReaderTCacheIn (local f r)
