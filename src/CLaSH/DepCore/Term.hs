{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module CLaSH.DepCore.Term
  ( Term (..)
  , Type
  , Binder (..)
  , ScopedTerm
  , ScopedType
  , LVar
  , CoreTerm
  , CoreType
  , CoreBinder
  , star
  , lam
  , pi_
  , let_
  )
where

import Bound                (Scope,(>>>=))
import Bound.Name           (Name(..),abstract1Name)
import Control.Applicative  (Applicative(..))
import Control.Monad        (ap)
import Data.Foldable        (Foldable(..))
import Data.Traversable     (Traversable(..))
import Prelude.Extras       (Eq1,Show1)

-- GHC API
import SrcLoc               (Located)
import FastString           (FastString)

data Binder n a
  = Lam { binderTy :: Name n a }
  | Pi  { binderTy :: Name n a }
  | Let { binderTy :: Name n a
        , binderTm :: Name n a
        }
  deriving (Foldable,Functor,Traversable,Show,Eq)

data Term n a
  = Var !a
  | Universe !Integer
  | App  !(Term n a) !(Term n a)
  | Bind !(Binder n (Term n a)) (Scope (Name n ()) (Term n) a)
  deriving (Foldable,Traversable,Functor,Eq,Show)

type Type = Term
type ScopedTerm n b a = Scope (Name n b) (Term n) a
type ScopedType n b a = ScopedTerm n b a

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

star :: CoreTerm
star = Universe 0

lam :: (LVar,CoreTerm) -> CoreTerm -> CoreTerm
lam (v,b) e = Bind (Lam (Name v b)) (abstract1Name v e)

pi_ :: (LVar,CoreTerm) -> CoreTerm -> CoreTerm
pi_ (v,b) e = Bind (Pi (Name v b)) (abstract1Name v e)

let_ :: (LVar,CoreTerm,CoreTerm) -> CoreTerm -> CoreTerm
let_ (v,ty,tm) e = Bind (Let (Name v ty) (Name v tm)) (abstract1Name v e)
