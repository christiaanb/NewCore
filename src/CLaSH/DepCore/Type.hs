module CLaSH.DepCore.Type where

import Bound                     (Scope (..))
import Bound.Name                (Name, name, instantiate1Name)
import Control.Comonad           (extract)

import CLaSH.DepCore.Environment (Env (..), declarePat, extendEnv)
import CLaSH.DepCore.Term        (Alt (..), Binder (..), FastString, Term (..), Type)
import CLaSH.DepCore.Util        (whnf)

inferType :: Eq a => Show n => Show a
          => Env n a   -- ^ Environment
          -> Term n a  -- ^ Term
          -> Type n a  -- ^ Inferred type
inferType env (Var a)       = lookupTy env a

inferType _   (Universe i)  = Universe (i+1)

inferType env (App e1 e2)   = if s == whnf env te
                                      then instantiate1Name e2 t
                                      else error "Mismatch"
  where
    te      = inferType env e2
    (_,s,t) = inferPi env (inferType env e1)

inferType env (Bind (Pi b) (Scope s)) = Universe (max k1 k2)
  where
    ty   = extract b
    env' = extendEnv inferType env ty Nothing
    k1   = inferUniverse env  (inferType env ty)
    k2   = inferUniverse env' (inferType env' s)

inferType env (Bind (Lam b) (Scope s)) = Bind (Pi b) (Scope (inferType env' s))
  where
    env' = extendEnv inferType env (extract b) Nothing

inferType env (Bind (Let ty tm) (Scope e2)) = instantiate1Name e1 (Scope t)
  where
    e1   = extract tm
    env' = extendEnv inferType env (extract ty) (Just e1)
    t    = inferType env' e2

inferType env (Case scrut alts) = undefined
  where
    sty           = inferType env scrut
    (tc,params)    = inferTCon env sty

    checkAlt (Alt n pat s) = undefined
      where
        decls = declarePat pat (TCon tc params)

inferPi :: Eq a => Show n => Show a
        => Env n a
        -> Type n a
        -> (n,Type n a,Scope (Name n ()) (Type n) a)
inferPi env ty = case whnf env ty of
                    Bind (Pi b) s -> (name b, extract b, s)
                    ty'           -> error ("Function expected: " ++ show ty)

inferUniverse :: Eq a => Show n => Show a
              => Env n a
              -> Type n a
              -> Integer
inferUniverse env ty = case whnf env ty of
                          Universe i -> i
                          ty'        -> error ("Type expected: " ++ show ty')

inferTCon :: Eq a => Show n => Show a
          => Env n a
          -> Type n a
          -> (FastString, [Type n a])
inferTCon env ty = case whnf env ty of
                     (TCon n params) -> (n,params)
                     ty'             -> error ("TCon expected: " ++ show ty')
