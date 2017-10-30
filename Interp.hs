{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE ScopedTypeVariables        #-}
module Interp where

import Data.IntMap as IMap
import Data.Map.Strict as Map
import Data.Set as Set
import Control.Applicative
import Data.Functor.Identity

import Control.Monad.Freer
import Control.Monad.Freer.Reader
import Control.Monad.Freer.Exception
import Control.Monad.Freer.Writer
import AbstractionEffects

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
-- Symbolic abstraction
  | Sym Var
    deriving (Show, Eq, Ord)

data PathExpression
  = P  Exp
  | PN Exp
    deriving (Show, Eq, Ord)

type PathCondition = Set.Set PathExpression

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
    deriving (Eq, Ord, Show)

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
       find :: Addr -> Eff m (Val n),
       ext  :: Addr -> Val n -> Eff m ()
     }

data Delta n m = Delta {
       delta  :: Op -> (Val n) -> (Val n) -> Eff m (Val n),
       isZero :: (Val n) -> Eff m Bool
     }

data Alloc m = Alloc {
       alloc :: Var -> Eff m Addr
     }

ev :: (Member (Reader [(Var, Addr)]) m, Num n) =>
      Delta n m -> Store n m -> Alloc m
   -> (Exp -> Eff m (Val n)) -> (Exp -> Eff m (Val n))
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
   Rec f e -> do a <- alloc f
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
  ext = \a v -> modifyStore (\sigma -> (a,v) : sigma)
  }

expectJust (Just a) = a

allocAt :: Member (StoreState [(Var, Addr)]) m => Alloc m
allocAt = Alloc {
  -- The extra type synonym is needed because effects.
  alloc = \x -> do sigma :: [(Var, Addr)] <- getStore
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

fix f = let a = f a in a

----------------------------------------
-- Standard semantics
----------------------------------------

-- mRun m = evalStateStore (runReaderT m []) []

mRun m = run (runStoreState (runReader m ([] :: [(Var, Addr)])) [])

eval e = mRun ((fix (ev deltaAt store allocAt)) e)

----------------------------------------
-- Failure semantics
----------------------------------------

failRun m = run (runStoreState (runError (runReader m ([] :: [(Var, Addr)]))) [])

evalFail e = failRun (fix (ev deltaFail store allocAt) e)

----------------------------------------
-- Trace semantics
----------------------------------------
{-
ev_tell ev0 ev e = do rho   <- ask
                      sigma <- getStore
                      tell [(e, rho, sigma)]
                      ev0 ev e

traceRun m = run (runWriter (runStoreState (runError (runReader m [])) []))

evalTrace e = traceRun (fix (ev_tell (ev deltaFail store allocAt)) e)
-}

----------------------------------------
-- Dead code Collecting semantics
----------------------------------------

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
  run $
  runError
  (runDeadState
   (runStoreState
    (runReader m ([] :: [(Var,Addr)]))
    [])
   Set.empty
   )

evalDead e = deadRun (eval_dead (fix (evDead (ev deltaAt store allocAt))) e)

----------------------------------------
-- Finitization
----------------------------------------
{-
deltaAbst = Delta {
  delta = \o m n -> case (o,m,n) of
      (Plus,  _, _) -> return (N NVal)
      (Minus, _, _) -> return (N NVal)
      (Mult,  _, _) -> return (N NVal)
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
                  forP (IMap.findWithDefault Set.empty a sigma) $ \v ->
                    return v,
  ext = \a v -> updateStore (IMap.insertWith Set.union a (Set.singleton v))
  }

forP :: (Foldable f, MonadPlus m) => f a -> (a -> m b) -> m b
forP t body = Prelude.foldr (\a r -> body a `mplus` r) mzero t

abstRun m = runND (runStateTStore (runExceptT (runReaderT m [])) IMap.empty)

evalAbst e = abstRun (fix (ev deltaAbst storeNd allocAbst) e)
-}
----------------------------------------
-- Caching
----------------------------------------
{-
evCache ev0 ev e = do
  rho <- ask
  sigma <- getStore
  let state = (e,rho,sigma)
  outC <- getCacheOut
  case Map.lookup state outC of
    Just valStoreSet ->
      forP valStoreSet $ \ (v, sigma') -> do
        putStore sigma'
        return v
    Nothing -> do
      inC <- askCacheIn
      let valStore0 = Map.findWithDefault Set.empty state inC
      putCacheOut (Map.insertWith Set.union state valStore0 outC)
      v <- ev0 ev e
      sigma' <- getStore
      let valStore' = (v,sigma')
      updateCacheOut (\out ->
        Map.insertWith Set.union state (Set.singleton valStore') out)
      return v

-- cacheRun m = runState (runReaderT (runNDT (runStateT (runExceptT (runReaderT m _) ) _) ) _) _

fixCache eval e = do
  rho <- ask
  sigma <- getStore
  let state = (e,rho,sigma)
  fixp <- mlfp (\fp -> do putCacheOut Map.empty
                          putStore sigma
                          localCacheIn (const fp) (eval e) -- ? const
                          getCacheOut)
  forP (Map.lookup state fixp) $ \(v,sigma) -> do
    putStore sigma
    return v

mlfp f = let loop x = do
               x' <- f x
               if x == x'
                 then return x
                 else loop x'
         in loop (∅)
-}
----------------------------------------
-- Store crush
----------------------------------------
{-
deltaPrecise = Delta {
  delta = \o m n -> case (o,m,n) of
      (Plus, N (IVal i), N (IVal j)) -> return (N (IVal (i+j)))
      (Plus, _, _) -> return (N NVal)
      (Minus, N (IVal i), N (IVal j)) -> return (N (IVal (i-j)))
      (Minus, _, _) -> return (N NVal)
      (Mult, N (IVal i), N (IVal j)) -> return (N (IVal (i*j)))
      (Mult, _, _) -> return (N NVal)
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


storeCrush = Store {
  find = \a -> do
      σ <- getStore
      forP (Map.findWithDefault Set.empty a σ) $ \v ->
        return v,
  ext = \a v ->
    updateStore (\σ -> if a `Map.member` σ
                       then Map.adjust (crush v) a σ
                       else Map.insert a (Set.singleton v) σ)
  }

crush :: Val N -> Set (Val N) -> Set (Val N)
crush v@(Clo _ _ _) vs = Set.insert v vs
crush v vs = Set.insert (N NVal) (Set.filter isClosure vs)

isClosure :: Val n -> Bool
isClosure (Clo _ _ _) = True
isClosure _           = False
-}
----------------------------------------
-- Symbolic Execution
----------------------------------------

-- This is going to require changing the value type!
{-
evSymbolic ev0 ev (Sym x) = return (Var x)
evSymbolic ev0 ev e       = ev0 ev e

deltaSymbolic = Delta {
  delta = \o n m ->
    case (o, n, m) of
      (Div, _, _) -> do
        z <- isZero m
        if z then fail
          else case (n, m) of
                 (N (IVal i), N (IVal j)) -> return (N (IVal (i `div`j)))
                 _ -> return
-}

----------------------------------------
-- Garbage Collection
----------------------------------------
{-
evCacheGC ev0 ev e = do
  rho   <- ask
  sigma <- getStore
  psi   <- askRoots
  let state = (e,rho,sigma,psi)
  outC <- getCacheOut
  case Map.lookup state outC of
    Just valStoreSet ->
      forP valStoreSet $ \ (v, sigma') -> do
        putStore sigma'
        return v
    Nothing -> do
      inC <- askCacheIn
      let valStore0 = Map.findWithDefault Set.empty state inC
      putCacheOut (Map.insertWith Set.union state valStore0 outC)
      v <- ev0 ev e
      sigma' <- getStore
      let valStore' = (v,sigma')
      updateCacheOut (\out ->
        Map.insertWith Set.union state (Set.singleton valStore') out)
      return v

fixCacheGC eval e = do
  rho   <- ask
  sigma <- getStore
  psi   <- askRoots
  let state = (e,rho,sigma,psi)
  fixp <- mlfp (\fp -> do putCacheOut Map.empty
                          putStore sigma
                          localCacheIn (const fp) (eval e) -- ? const
                          getCacheOut)
  forP (Map.lookup state fixp) $ \(v,sigma) -> do
    putStore sigma
    return v
-}

{- Doesn't type check at the moment
evCollect ev0 ev e = do
  psi <- askRoots
  v   <- (ev0 ev) e
  updateStore (gc (Set.union psi (rootsV v)))
  return v
-}
gc = undefined
rootsV = undefined

{- Doesn't type check at the moment
evRoots (Delta {..}) _ _ ev0 ev (If e0 e1 e2) = do
  rho <- askEnv
  let psi = Set.union (roots e1 rho) (roots e2 rho)
  v <- extraRoots psi (ev e0)
  b <- isTruish v
  ev (If b e1 e2)
evRoots (Delta {..}) _ _ ev0 ev (Op2 o e0 e1) = do
  rho <- askEnv
  v0  <- extraRoots (roots e1 rho) (ev e0)
  v1  <- extraRoots (rootsV v0)    (ev e1)
  delta o v0 v1
evRoots _ (Store {..}) (Alloc {..}) ev0 ev (App e0 e1) = do
  rho <- askEnv
  v0  <- extraRoots (roots e1 rho) (ev e0)
  v1  <- extraRoots (rootsV v0)    (ev e1)
  case v0 of
    Clo x e2 rho' -> do
      a <- alloc x
      ext a v1
      localEnv (const ((x,a):rho')) (ev e2)
evRoots _ _ _ ev0 ev e =
  ev0 ev e
-}

askRoots = undefined
extraRoots = undefined
isTruish = undefined
roots = undefined

evRun = undefined

-- evalGC e = evRun (fixCache (fix (evCacheGC (evCollect (evRoots deltaAbst storeNd allocAbst (ev deltaAbst storeNd allocAbst)))))) e

----------------------------------------
-- Examples
----------------------------------------

exAbst = (App (Lam 0 (Op2 Plus (App (Var 0) (Num 1)) (App (Var 0)(Num 2)))) (Lam 1 (Var 1)))
--resAbst = evalAbst exAbst

exAbst' = let_ (lam (\x -> x)) (\f ->
          (App (App (lam (\y -> lam (\z -> z))) (App f 1)) (App f 2)))

-- A shallow embedding to write examples in an easy fashion.

let_ :: Exp -> (Exp -> Exp) -> Exp
let_ foo bar = App (Lam v body) foo
  where (v, body) = bind bar

lam :: (Exp -> Exp) -> Exp
lam f = Lam v body
  where (v, body) = bind f

bind :: (Exp -> Exp) -> (Var, Exp)
bind f = (v, body)
  where v    = newVar body
        body = f (Var v)

newVar :: Exp -> Var
newVar (Var _) = 0
newVar (Num _) = 0
newVar (If e0 e1 e2) = newVar e0 ⊔ newVar e1 ⊔ newVar e2
newVar (Op2 _ e0 e1) = newVar e0 ⊔ newVar e1
newVar (App e0 e1)   = newVar e0 ⊔ newVar e1
newVar (Rec v _) = v + 1
newVar (Lam v _) = v + 1

v1 ⊔ v2 = max v1 v2

----------------------------------------
-- Notation
----------------------------------------

class Empty a where
  (∅) :: a

instance Ord a => Empty (Set.Set a) where
  (∅) = Set.empty

instance Ord k => Empty (Map.Map k v) where
  (∅) = Map.empty

instance Empty (IMap.IntMap v) where
  (∅) = IMap.empty
