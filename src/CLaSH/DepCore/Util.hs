{-# LANGUAGE ScopedTypeVariables #-}
module CLaSH.DepCore.Util where

import Bound.Name                (instantiate1Name)
import Control.Comonad           (extract)

import CLaSH.DepCore.Term        (Binder (..), Term (..))
import CLaSH.DepCore.Environment (Env (..))

whnf :: Env n a
     -> Term n a
     -> Term n a
whnf = whnf' True

whnf' :: Bool
      -> Env n a
      -> Term n a
      -> Term n a
whnf' b env (Var x) =
  case lookupDef env x of
    Just d  -> whnf' b env d
    _       -> Var x

whnf' b env (App t1 t2) =
  case whnf' b env t1 of
    Bind (Lam _) s -> whnf' b env (instantiate1Name t2 s)
    Var x          -> App (Var x) (whnf' b env t2)
    nf             -> App nf t2

whnf' b env (Bind (Let _ e1) e2) =
  whnf' b env (instantiate1Name (extract e1) e2)

whnf' _ _ tm = tm
