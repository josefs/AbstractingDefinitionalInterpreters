{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
module AbstractionEffects where

import Control.Monad.Freer

import Control.Monad.Freer.Internal
import Data.Proxy

----------------------------------------
-- Store
----------------------------------------

data StoreState s v where
  GetStore :: StoreState s s
  PutStore :: !s -> StoreState s ()

-- | Retrieve state
getStore :: Member (StoreState s) r => Eff r s
getStore = send GetStore

-- | Store state
putStore :: Member (StoreState s) r => s -> Eff r ()
putStore s = send (PutStore s)

-- | Modify state
modifyStore :: Member (StoreState s) r => (s -> s) -> Eff r ()
modifyStore f = fmap f getStore >>= putStore

-- | Handler for State effects
runStoreState :: Eff (StoreState s ': r) w -> s -> Eff r (w,s)
runStoreState (Val x) s = return (x,s)
runStoreState (E u q) s = case decomp u of
  Right GetStore      -> runStoreState (qApp q s) s
  Right (PutStore s') -> runStoreState (qApp q ()) s'
  Left  u'            -> E u' (tsingleton (\x -> runStoreState (qApp q x) s))

----------------------------------------
-- Dead
----------------------------------------

data DeadState s v where
  GetDead :: DeadState s s
  PutDead :: !s -> DeadState s ()

-- | Retrieve state
getDead :: Member (DeadState s) r => Eff r s
getDead = send GetDead

-- | Dead state
putDead :: Member (DeadState s) r => s -> Eff r ()
putDead s = send (PutDead s)

-- | Modify state
modifyDead :: Member (DeadState s) r => (s -> s) -> Eff r ()
modifyDead f = fmap f getDead >>= putDead

-- | Handler for State effects
runDeadState :: Eff (DeadState s ': r) w -> s -> Eff r (w,s)
runDeadState (Val x) s = return (x,s)
runDeadState (E u q) s = case decomp u of
  Right GetDead      -> runDeadState (qApp q s) s
  Right (PutDead s') -> runDeadState (qApp q ()) s'
  Left  u'            -> E u' (tsingleton (\x -> runDeadState (qApp q x) s))

----------------------------------------
-- CacheOut
----------------------------------------

data CacheOutState s v where
  GetCacheOut :: CacheOutState s s
  PutCacheOut :: !s -> CacheOutState s ()

-- | Retrieve state
getCacheOut :: Member (CacheOutState s) r => Eff r s
getCacheOut = send GetCacheOut

-- | CacheOut state
putCacheOut :: Member (CacheOutState s) r => s -> Eff r ()
putCacheOut s = send (PutCacheOut s)

-- | Modify state
modifyCacheOut :: Member (CacheOutState s) r => (s -> s) -> Eff r ()
modifyCacheOut f = fmap f getCacheOut >>= putCacheOut

-- | Handler for State effects
runCacheOutState :: Eff (CacheOutState s ': r) w -> s -> Eff r (w,s)
runCacheOutState (Val x) s = return (x,s)
runCacheOutState (E u q) s = case decomp u of
  Right GetCacheOut      -> runCacheOutState (qApp q s) s
  Right (PutCacheOut s') -> runCacheOutState (qApp q ()) s'
  Left  u'               -> E u' (tsingleton (\x -> runCacheOutState (qApp q x) s))

----------------------------------------
-- CacheIn
----------------------------------------

data ReaderCacheIn e v where
  ReaderCacheIn :: ReaderCacheIn e e

-- | Request a value for the environment
askCacheIn :: (Member (ReaderCacheIn e) r) => Eff r e
askCacheIn = send ReaderCacheIn

-- | Handler for reader effects
runReaderCacheIn :: Eff (ReaderCacheIn e ': r) w -> e -> Eff r w
runReaderCacheIn m e = handleRelay return (\ReaderCacheIn k -> k e) m

localCacheIn :: forall e a r. Member (ReaderCacheIn e) r =>
                (e -> e) -> Eff r a -> Eff r a
localCacheIn f m = do
  e0 <- askCacheIn
  let e = f e0
  let h :: ReaderCacheIn e v -> Arr r v a -> Eff r a
      h ReaderCacheIn g = g e
  interpose return h m
