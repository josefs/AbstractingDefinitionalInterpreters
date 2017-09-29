{-# LANGUAGE RecordWildCards #-}
module Interp where

import Control.Monad.Reader
import Control.Monad.State

type Var = Int

type Numb = Int

data Exp =
    Var Var
  | Num Numb
  | If Exp Exp Exp
  | Op2 Op Exp Exp
  | App Exp Exp
  | Rec Var Exp
  | Lam Var Exp

data Op =
    Plus
  | Minus
  | Mult
  | Div

data Val =
    N Numb
  | Clo Var Exp (Exp -> Val)

data Store m = Store {
       find :: Var -> m Val,
       ext  :: Var -> Val -> m ()
     }

data Delta m = Delta {
       delta  :: Op -> Val -> Val -> Val,
       isZero :: Val -> m Val
     }

data Alloc m = Alloc {
       alloc :: Var -> m Val
     }

ev eval (Delta {..}) (Store {..}) (Alloc {..})e = case e of
   Num n -> return n
   Var x -> do rho <- ask
   	       find (rho x)
   If e0 e1 e2 -> do v <- eval e0
   	       	     z <- isZero v
	             eval (if z then e1 else e2)
   Op2 o e0 e1 -> do v0 <- eval e0
   	       	     v1 <- eval e1
		     delta o v0 v1
   Rec f e -> do rho <- ask
   	       	 a <- alloc f
		 let rho' = rho f a
		 v <- local rho' (eval e)
		 ext a v
		 return v
   Lam x e -> do rho <- ask
   	         return (Clo x e rho)
   App e0 e1 -> do (Clo x e2 rho) <- eval e0
   	     	   v1 <- eval e1
		   a  <- alloc x
		   ext a v1
		   local (rho x a) (eval e2)

{-
class Interp a where
  ask
  env
  find
  ext
  isZero :: Var -> m Val
-}
