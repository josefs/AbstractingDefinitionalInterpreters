{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE FlexibleContexts           #-}
module Interp2 where

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Writer
import AbstractionMonads
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
  | IVal Int

instance Eq N where
  NVal == NVal = True
  IVal i == IVal j = i == j
  _ == _ = False

instance Ord N where
  _ <= _ = True

instance Num N where
  IVal i + IVal j = IVal (i+j)
  _ + _ = NVal
  IVal i - IVal j = IVal (i-j)
  _ - _ = NVal
  IVal i * IVal j = IVal (i*j)
  _ * _ = NVal
  fromInteger i = IVal (fromInteger i)
  abs (IVal i) = IVal (abs i)
  abs _ = NVal
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
      (Plus, N (IVal i), N (IVal j)) -> return (N (IVal (i+j)))
      (Plus, _, _) -> return (N NVal)
      (Div , N (IVal i) , N (IVal n)) ->
        if n == 0
        then throwError "Division by zero"
        else return (N (IVal (i `div` n)))
      (Div, _, N NVal) ->
        mplus (throwError "Division by zero")
              (return (N NVal)),
  isZero = \v -> case v of
      N NVal -> mplus (return True)
                      (return False)
      N (IVal n) -> return (n == 0)
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
