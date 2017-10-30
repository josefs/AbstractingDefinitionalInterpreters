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

