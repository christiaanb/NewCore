{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module CLaSH.DepCore.Term where

import Bound
import Bound.Name
import Bound.Var
import Control.Applicative
import Control.Comonad
import Control.Monad
import Data.Foldable
import Data.Traversable
import Prelude.Extras

import Control.DeepSeq

data Binder n a
  = Lam {binder :: Name n a}
  | Pi  {binder :: Name n a}
  deriving (Foldable,Functor,Traversable,Show,Eq)

instance (NFData n, NFData a) => NFData (Name n a) where
  rnf (Name n b) = rnf n `seq` rnf b `seq` ()

instance (NFData n, NFData a) => NFData (Binder n a) where
  rnf (Lam b) = rnf b `seq` ()
  rnf (Pi  b) = rnf b `seq` ()

instance Comonad (Binder n) where
  extract    = extract . binder
  extend f w = fmap (const (f w)) w

data Term n a
  = Var !a
  | Universe !Integer
  | App  !(Term n a) !(Term n a)
  | Bind !(Binder n (Term n a)) (Scope (Name n ()) (Term n) a)
  deriving (Foldable,Traversable,Functor,Eq,Show)

instance Eq1 (Term n)
instance Show n => Show1 (Term n)

instance (NFData b, NFData a) => NFData (Var b a) where
  rnf (F a) = rnf a `seq` ()
  rnf (B b) = rnf b `seq` ()

instance (NFData n, NFData a) => NFData (Term n a) where
  rnf (Var a           ) = rnf a `seq` ()
  rnf (Universe i      ) = rnf i `seq` ()
  rnf (App l r         ) = rnf l `seq` rnf r `seq` ()
  rnf (Bind b (Scope s)) = rnf b `seq` rnf s `seq` ()

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

inferPi :: Eq a => Show n => Show a
        => Term n a
        -> (n,Term n a,Scope (Name n ()) (Term n) a)
inferPi (Bind (Pi b) s) = (name b, extract b, s)
inferPi ty              = error ("Function expected: " ++ show ty)

inferUniverse :: Eq a => Show n => Show a
              => Term n a
              -> Integer
inferUniverse (Universe i) = i
inferUniverse ty           = error ("Type expected: " ++ show ty)

inferType :: Eq a  => Show n => Show a
          => (a -> Term n a) -- ^ Context
          -> Term n a        -- ^ Term
          -> Term n a        -- ^ Inferred type
inferType ctx (Var a)          = ctx a
inferType _   (Universe i)     = Universe (i+1)
inferType ctx (App e1 e2)      = if s == te then instantiate1Name e2 t
                                            else error "Mismatch"
  where
    te      = inferType ctx e2
    (_,s,t) = inferPi (inferType ctx e1)
inferType ctx (Bind (Pi b) s)  = Universe (max k1 k2)
  where
    t  = extract b
    k1 = inferUniverse (inferType ctx t)
    k2 = inferUniverse (inferType ctx (instantiate1Name t s))
inferType ctx (Bind (Lam b) s) = Bind (Pi b) s'
  where
    -- s'     = toScope . inferType ctx' . fromScope $ s
    -- ctx'   = unvar bCtx fCtx
    -- bCtx _ = fmap F . extract $ b
    -- fCtx   = fmap F . ctx
    s'     = Scope . inferType ctx' . unscope $ s
    ctx'   = unvar bCtx fCtx
    bCtx _ = fmap (F . Var) . extract $ b
    fCtx   = fmap (F . Var) . inferType ctx

-- Example:
type LVar = String
type CoreTerm = Term LVar LVar

uni :: CoreTerm
uni = Universe 0

lam :: (LVar,CoreTerm) -> CoreTerm -> CoreTerm
lam (v,b) e = Bind (Lam (Name v b)) (abstract1Name v e)

pi_ :: (LVar,CoreTerm) -> CoreTerm -> CoreTerm
pi_ (v,b) e = Bind (Pi (Name v b)) (abstract1Name v e)

example :: CoreTerm
example = lam ("p",uni) $ lam ("q",uni) $ lam ("m",pi_("_",uni) uni) $ lam ("a",uni) $ lam ("b",uni)
        $ lam ("c",pi_("_",uni) uni)
        $ lam ("d",pi_("_",uni) (pi_("_",uni) uni))
        $ lam ("e",pi_("_",uni) uni)
        $ lam ("g",pi_("_",uni) (pi_("_",uni) (pi_("_",uni) uni)))
        $ lam ("h",pi_("_",uni) uni)
        $ lam ("g",pi_("_",uni) (pi_("_",uni) (pi_("_",uni) uni)))
        $ lam ("f",pi_ ("_",App (App (Var "g") (Var "a")) (Var "c")) (Var "b"))
        $ lam ("f1",pi_ ("_",App (App (Var "g") (Var "a")) (Var "c")) (Var "b"))
        $ lam ("f2",pi_ ("_",App (App (Var "g") (Var "a")) (Var "c")) (Var "b"))
        $ lam ("f3",pi_ ("_",App (App (Var "g") (Var "a")) (Var "c")) (Var "b"))
        $ lam ("f4",pi_ ("_",App (App (Var "g") (Var "a")) (Var "c")) (Var "b"))
        $ lam ("f5",pi_ ("_",App (App (Var "g") (Var "a")) (Var "c")) (Var "b"))
        $ lam ("f6",pi_ ("_",App (App (Var "g") (Var "a")) (Var "c")) (Var "b"))
        $ lam ("f7",pi_ ("_",App (App (Var "g") (Var "a")) (Var "c")) (Var "b"))
        $ lam ("f8",pi_ ("_",App (App (Var "g") (Var "a")) (Var "c")) (Var "b"))
        $ lam ("k",pi_ ("_",Var "b") (Var "e"))
        $ lam ("y",pi_ ("_",Var "e") (Var "h"))
        $ lam ("x",App (App (Var "g") (Var "a")) (Var "c"))
        $ App (Var "y") (App (Var "k") (App (Var "f") (Var "x")))
