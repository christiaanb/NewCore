{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, KindSignatures #-}
module CLaSH.DepCore.Term
  ( Term (..)
  , Type
  , Alt (..)
  , Binder (..)
  , ScopedTerm
  , ScopedType
  , FastString
  , LVar
  , CoreTerm
  , CoreType
  , CoreBinder
  , star
  , lam
  , pi_
  , let_
  , varp
  , wildp
  , litp
  , conp
  , alt
  )
where

import Bound                (Scope, Bound (..), abstract)
import Bound.Name           (Name(..), abstract1Name)
import Control.Applicative  (Applicative(..))
import Control.Monad        (ap)
import Data.Foldable        (Foldable(..))
import Data.List            (elemIndex)
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
  | TCon !FastString ![Term n a]
  | DCon !FastString ![Term n a]
  | Case !(Term n a) ![Alt (Term n) a]
  deriving (Foldable,Traversable,Functor,Eq,Show)

data Pat (f :: * -> *) a
  = VarP
  | WildP
  | LitP !Integer
  | ConP FastString [Pat f a]
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

instance Bound Pat where
  VarP      >>>= _ = VarP
  WildP     >>>= _ = WildP
  LitP i    >>>= _ = LitP i
  ConP g ps >>>= f = ConP g (map (>>>= f) ps)

data Alt f a = Alt !Int (Pat f a) (Scope Int f a)
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

instance Bound Alt where
  Alt n p b >>>= f = Alt n (p >>>= f) (b >>>= f)

type LVar = Located FastString
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
  TCon tc es -> TCon tc (map (`bindTerm` f) es)
  DCon dc es -> DCon dc (map (`bindTerm` f) es)
  Case e as  -> Case (e `bindTerm` f) (map (>>>= f) as)

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

data P n a = P { pattern :: [a] -> Pat (Term n) a, bindings :: [a] }

varp :: a -> P n a
varp a = P (const VarP) [a]

wildp :: P n a
wildp = P (const WildP) []

litp :: Integer -> P n a
litp i = P (const (LitP i)) []

conp :: FastString -> [P n a] -> P n a
conp g ps = P (ConP g . go ps) (ps >>= bindings)
  where
    go (P p as:ps) bs = p bs : go ps (bs ++ as)
    go [] _ = []

alt :: Eq a => P n a -> Term n a -> Alt (Term n) a
alt (P p as) t = Alt (length as) (p []) (abstract (`elemIndex` as) t)
