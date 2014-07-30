{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module CLaSH.DepCore.Term
  ( Term (..)
  , Type
  , Binder (..)
  , LVar
  , CoreTerm
  , CoreType
  , CoreBinder
  , uni
  , lam
  , pi_
  )
where

import Bound                (Scope,(>>>=))
import Bound.Name           (Name(..),abstract1Name)
import Control.Applicative  (Applicative(..))
import Control.Comonad      (Comonad(..))
import Control.Monad        (ap)
import Data.Foldable        (Foldable(..))
import Data.Traversable     (Traversable(..))
import Prelude.Extras       (Eq1,Show1)

-- GHC API
import SrcLoc               (Located)
import FastString           (FastString)

data Binder n a
  = Lam {binder :: Name n a}
  | Pi  {binder :: Name n a}
  deriving (Foldable,Functor,Traversable,Show,Eq)

instance Comonad (Binder n) where
  extract    = extract . binder
  extend f w = fmap (const (f w)) w

data Term n a
  = Var !a
  | Universe !Integer
  | App  !(Term n a) !(Term n a)
  | Bind !(Binder n (Term n a)) (Scope (Name n ()) (Term n) a)
  deriving (Foldable,Traversable,Functor,Eq,Show)

type Type = Term

instance Eq1 (Term n)
instance Show n => Show1 (Term n)

instance Applicative (Term n) where
  pure  = Var
  (<*>) = ap

instance Monad (Term n) where
  return = Var
  (>>=)  = bindTerm

bindTerm :: Term n a -> (a -> Term n b) -> Term n b
bindTerm tm f = case tm of
  Var a      -> f a
  Universe i -> Universe i
  App e1 e2  -> App (bindTerm e1 f) (bindTerm e2 f)
  Bind b s   -> Bind (fmap (`bindTerm` f) b) (s >>>= f)

type LVar         = Located FastString
type CoreTerm     = Term LVar LVar
type CoreType     = Type LVar LVar
type CoreBinder a = Binder LVar a

uni :: CoreTerm
uni = Universe 0

lam :: (LVar,CoreTerm) -> CoreTerm -> CoreTerm
lam (v,b) e = Bind (Lam (Name v b)) (abstract1Name v e)

pi_ :: (LVar,CoreTerm) -> CoreTerm -> CoreTerm
pi_ (v,b) e = Bind (Pi (Name v b)) (abstract1Name v e)
