{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE UndecidableInstances       #-}
module Interp2 where

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Writer
import Control.Monad.Logic
--import MyLogicT
import Data.IntMap as Map
import Data.Set as Set
import Control.Applicative
import Data.Functor.Identity

type Var = Int

type Numb = Int

type Addr = Int

data Exp =
    Var Var
  | Num Numb
  | If Exp Exp Exp
  | Op2 Op Exp Exp
  | App Exp Exp
  | Rec Var Exp
  | Lam Var Exp
    deriving (Show, Eq, Ord)

instance Num Exp where
  e1 + e2 = Op2 Plus  e1 e2
  e1 - e2 = Op2 Minus e1 e2
  e1 * e2 = Op2 Mult  e1 e2
  fromInteger i = Num (fromInteger i)
  abs = error "abs undefined"
  signum = error "signum undefined"

data Op =
    Plus
  | Minus
  | Mult
  | Div
    deriving (Show, Eq, Ord)

data Val n =
    N n
  | Clo Var Exp [(Var, Addr)]
    deriving (Show, Eq, Ord)

instance Num n => Num (Val n) where
  N m + N n = N (m + n)
  N m - N n = N (m - n)
  N m * N n = N (m * n)
  fromInteger n = N (fromInteger n)
  abs (N m) = N (abs m)
  signum = error "signum for Val undefined"

data N = NVal

instance Eq N where
  _ == _ = True

instance Ord N where
  _ <= _ = True

instance Num N where
  NVal + NVal = NVal
  NVal - NVal = NVal
  NVal * NVal = NVal
  fromInteger _ = NVal
  abs NVal = NVal
  signum = error "signum for N undefined"

data Store n m = Store {
       find :: Addr -> m (Val n),
       ext  :: Addr -> Val n -> m ()
     }

data Delta n m = Delta {
       delta  :: Op -> (Val n) -> (Val n) -> m (Val n),
       isZero :: (Val n) -> m Bool
     }

data Alloc m = Alloc {
       alloc :: Var -> m Addr
     }

ev :: (MonadReader [(Var, Addr)] m, Num n) =>
      Delta n m -> Store n m -> Alloc m
   -> (Exp -> m (Val n)) -> (Exp -> m (Val n))
ev (Delta {..}) (Store {..}) (Alloc {..}) eval e =
  case e of
   Num n -> return (fromIntegral n)
   Var x -> do rho <- ask
               find (expectJust (Prelude.lookup x rho))
   If e0 e1 e2 -> do v <- eval e0
                     z <- isZero v
                     eval (if z then e1 else e2)
   Op2 o e0 e1 -> do v0 <- eval e0
                     v1 <- eval e1
                     delta o v0 v1
   Rec f e -> do rho <- ask
                 a <- alloc f
                 v <- local ((f,a):) (eval e)
                 ext a v
                 return v
   Lam x e -> do rho <- ask
                 return (Clo x e rho)
   App e0 e1 -> do (Clo x e2 rho) <- eval e0
                   v1 <- eval e1
                   a  <- alloc x
                   ext a v1
                   local ((x,a) :) (eval e2)

store = Store {
  find = \a -> do sigma <- getStore
                  return (expectJust $ Prelude.lookup a sigma),
  ext = \a v -> updateStore (\sigma -> (a,v) : sigma)
  }

expectJust (Just a) = a

allocAt = Alloc {
  alloc = \x -> do sigma <- getStore
                   return (length sigma)
  }

deltaAt = Delta {
  delta = \o n m -> return $  case (o,n,m) of
      (Plus,  N a, N b) -> N (a + b)
      (Minus, N a, N b) -> N (a - b)
      (Mult,  N a, N b) -> N (a * b)
      (Div,   N a, N b) -> N (a `div` b),
  isZero = \(N i) -> return (i == 0)
  }

deltaFail = deltaAt {
  delta = \o n m -> case (o,n,m) of
      (Div, _, N 0) -> throwError "Division by zero"
      _ -> delta (deltaAt) o n m
  }

-- Standard semantics

mRun m = evalStateStore (runReaderT m []) []

eval e = mRun ((fix (ev deltaAt store allocAt)) e)

-- Failure semantics

failRun m = runStateStore (runExceptT (runReaderT m [])) []

evalFail e = failRun (fix (ev deltaFail store allocAt) e)

-- Trace semantics

ev_tell ev0 ev e = do rho   <- ask
                      sigma <- getStore
                      tell [(e, rho, sigma)]
                      ev0 ev e

traceRun m = runWriter (runStateTStore (runExceptT (runReaderT m [])) [])

evalTrace e = traceRun (fix (ev_tell (ev deltaFail store allocAt)) e)


-- Dead code Collecting semantics
-- This requires two state monads which is not so convenient with
-- the mtl approach. I need to think about how to do it better.

evDead ev0 ev e = do
  theta <- getDead
  putDead (Set.delete e theta)
  ev0 ev e

eval_dead eval e = do
  putDead (subExps e)
  eval e

subExps e@(Var _) = Set.singleton e
subExps e@(Num _) = Set.singleton e
subExps e@(If e1 e2 e3) = Set.unions [Set.singleton e
                                     ,subExps e1
                                     ,subExps e2
                                     ,subExps e3]
subExps e@(Op2 _ e1 e2) = Set.unions [Set.singleton e
                                     ,subExps e1
                                     ,subExps e2]
subExps e@(App e1 e2) = Set.unions [Set.singleton e
                                   ,subExps e1
                                   ,subExps e2]
subExps e@(Rec _ e1) = Set.unions [Set.singleton e
                                   ,subExps e1]
subExps e@(Lam _ e1) = Set.unions [Set.singleton e
                                  ,subExps e1]


deadRun m =
  runExcept
  (runStateTDead
   (runStateTStore
    (runReaderT m [])
    [])
   Set.empty
   )

evalDead e = deadRun (eval_dead (fix (evDead (ev deltaAt store allocAt))) e)

-- Finitization

deltaAbst = Delta {
  delta = \o m n -> case (o,m,n) of
      (Plus, _, _) -> return (N (Left NVal))
      (Div , _, N (Right n)) -> if n == 0
                                      then throwError "Division by zero"
                                      else return (N (Left NVal))
      (Div, _, N (Left NVal)) ->
        mplus (throwError "Division by zero")
        (return (N (Left NVal))),
  isZero = \v -> case v of
      N (Left NVal) -> mplus (return True)
                             (return False)
      N (Right n) -> return (n == 0)
  }

allocAbst = Alloc {
  alloc = return
  }

storeNd = Store {
  find = \a -> do sigma <- getStore
                  forP (findWithDefault Set.empty a sigma) $ \v ->
                    return v,
  ext = \a v -> updateStore (Map.insertWith Set.union a (Set.singleton v))
  }

forP :: (Foldable f, MonadPlus m) => f a -> (a -> m b) -> m b
forP t body = Prelude.foldr (\a r -> body a `mplus` r) mzero t 

abstRun m = runND (runStateTStore (runExceptT (runReaderT m [])) Map.empty)

evalAbst e = abstRun (fix (ev deltaAbst storeNd allocAbst) e)

-- Specialized reader monads

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

-- Specialized state monads

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

-- StateTDead

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

{-
instance MonadLogic m => MonadLogic (StateTDead s m) where
  msplit  sm = mkStateTDead $ \s ->
    do r <- msplit (runStateTDead sm s)
       case r of
         Nothing          -> return (Nothing, s)
         Just ((a,s'), m) ->
             return (Just (a, mkStateTDead (\_ -> m)), s')

  interleave ma mb = mkStateTDead $ \s ->
                        runStateTDead ma s `interleave` runStateTDead mb s

  ma >>- f = mkStateTDead $ \s ->
                runStateTDead ma s >>- \(a,s') -> runStateTDead (f a) s'

  ifte t th el = mkStateTDead $ \s ->
                     ifte (runStateTDead t s)
                          (\(a,s') -> runStateTDead (th a) s')
                          (runStateTDead el s)
-}
-- Instead of using MonadLogic, which doesn't support
-- GeneralizedNewtypeDeriving, I'm just going to stick to MonadPlus
-- and roll my own non-determinism monad.

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
