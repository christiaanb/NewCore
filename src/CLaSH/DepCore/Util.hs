{-# LANGUAGE ScopedTypeVariables #-}
module CLaSH.DepCore.Util where

import Bound           (Scope (..),fromScope)
import Bound.Name      (Name,name,instantiate1Name)
import Bound.Var
import Control.Comonad (extract)

import CLaSH.DepCore.Term

inferType :: Eq a => Show n => Show a
          => (a -> Type n a)         -- ^ Context
          -> (a -> Maybe (Term n a)) -- ^ Definitions
          -> Term n a                -- ^ Term
          -> Type n a                -- ^ Inferred type
inferType ctx _ (Var a)          = ctx a
inferType _   _ (Universe i)     = Universe (i+1)
inferType ctx defs (App e1 e2)   = if s == whnf defs te
                                      then instantiate1Name e2 t
                                      else error "Mismatch"
  where
    te      = inferType ctx defs e2
    (_,s,t) = inferPi defs (inferType ctx defs e1)
inferType ctx defs (Bind (Pi b) s)  = Universe (max k1 k2)
  where
    t  = extract b
    k1 = inferUniverse defs  (inferType ctx defs t)
    k2 = inferUniverse defs' (inferType ctx' defs' (fromScope s))

    defs' = unvar (const Nothing)    (fmap (fmap F) . defs)
    ctx'  = unvar (fmap F . const t) (fmap F . ctx)

inferType ctx defs (Bind (Lam b) s) = Bind (Pi b) (inferInScope (extract b) ctx defs s)

type ScopedTerm n a = Scope (Name n ()) (Term n) a
type ScopedType n a = ScopedTerm n a

inferInScope :: Eq a => Show n => Show a
             => Term n a
             -> (a -> Type n a)
             -> (a -> Maybe (Term n a))
             -> ScopedTerm n a
             -> ScopedType n a
inferInScope bTerm ctx defs (Scope s) = Scope (inferType ctx' defs' s)
  where
    ctx' (B _)  = fmap (F . Var) bTerm
    ctx' (F tm) = fmap (F . Var) (inferType ctx defs tm)

    defs' (B _)       = Nothing
    defs' (F (Var x)) = fmap (fmap (F . Var)) (defs x)
    defs' (F tm)      = Just (fmap (F . Var) tm)

inferPi :: Eq a => Show n => Show a
        => (a -> Maybe (Term n a))
        -> Type n a
        -> (n,Type n a,Scope (Name n ()) (Type n) a)
inferPi defs ty = case whnf defs ty of
                    Bind (Pi b) s -> (name b, extract b, s)
                    ty'           -> error ("Function expected: " ++ show ty)

inferUniverse :: Eq a => Show n => Show a
              => (a -> Maybe (Term n a))
              -> Type n a
              -> Integer
inferUniverse defs ty = case whnf defs ty of
                          Universe i -> i
                          ty'        -> error ("Type expected: " ++ show ty')

whnf :: (a -> Maybe (Term n a)) -- ^ Definitions
     -> Term n a
     -> Term n a
whnf = whnf' True

whnf' :: Bool
      -> (a -> Maybe (Term n a))
      -> Term n a
      -> Term n a
whnf' b defs (Var x) =
  case defs x of
    Just d  -> whnf' b defs d
    _       -> Var x

whnf' b defs (App t1 t2) =
  case whnf' b defs t1 of
    Bind (Lam _) s -> whnf' b defs (instantiate1Name t2 s)
    Var x          -> App (Var x) (whnf' b defs t2)
    nf             -> App nf t2

whnf' _ _ tm = tm
