{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleContexts #-}
module Interp where

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Writer

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
    deriving Show

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
    deriving Show

data Val =
    N Numb
  | Clo Var Exp [(Var, Addr)]
    deriving Show

data Store m = Store {
       find :: Addr -> m Val,
       ext  :: Addr -> Val -> m ()
     }

data Delta m = Delta {
       delta  :: Op -> Val -> Val -> m Val,
       isZero :: Val -> m Bool
     }

data Alloc m = Alloc {
       alloc :: Var -> m Addr
     }

ev :: MonadReader [(Var, Addr)] m =>
      Delta m -> Store m -> Alloc m
   -> (Exp -> m Val) -> (Exp -> m Val)
ev (Delta {..}) (Store {..}) (Alloc {..}) eval e =
  case e of
   Num n -> return (N n)
   Var x -> do rho <- ask
               find (expectJust (lookup x rho))
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
  find = \a -> do sigma <- get
                  return (expectJust $ lookup a sigma),
  ext = \a v -> modify (\sigma -> (a,v) : sigma)
  }

expectJust (Just a) = a

allocAt = Alloc {
  alloc = \x -> do sigma <- get
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

mRun m = evalState (runReaderT m []) []

eval e = mRun ((fix (ev deltaAt store allocAt)) e)

-- Failure semantics

failRun m = runState (runExceptT (runReaderT m [])) []

evalFail e = failRun (fix (ev deltaFail store allocAt) e)

-- Trace semantics

ev_tell ev0 ev e = do rho   <- ask
                      sigma <- get
                      tell [(e, rho, sigma)]
                      ev0 ev e

traceRun m = runWriter (runStateT (runExceptT (runReaderT m [])) [])

evalTrace e = traceRun (fix (ev_tell (ev deltaFail store allocAt)) e)


-- Dead code Collecting semantics
-- This requires two state monads which is not so convenient with
-- the mtl approach. I need to think about how to do it better.
{-
ev_dead ev0 ev e = do
  theta <- get
  put (delete e theta)
  ev0 ev e
-}
