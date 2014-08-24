module CLaSH.DepCore.Environment where

import Bound              (Scope (..))
import Bound.Var          (Var (..))
import Data.Functor       ((<$>))

import CLaSH.DepCore.Term (Term (..), Type)

data Env n a = Env
             { lookupTy  :: a -> Type n a
             , lookupDef :: a -> Maybe (Term n a)
             }

extendEnv :: Eq a => Show n => Show a
          => (Env n a -> Term n a -> Type n a) -- ^ Type inference (for lifted terms)
          -> Env n a                           -- ^ Current environment
          -> Type n a                          -- ^ Type to add
          -> Maybe (Term n a)                  -- ^ Term to Add
          -> Env n (Var b (Term n a))          -- ^ Environment for scoped variable
extendEnv inferType env@(Env ctx defs) bType bTerm = Env ctx' defs'
  where
    ctx' (B _)  = F . Var <$> bType
    ctx' (F tm) = F . Var <$> inferType env tm

    defs' (B _)       = Nothing
    defs' (F (Var x)) = fmap (F . Var) <$> defs x
    defs' (F tm)      = Just (F . Var <$> tm)

declarePat  = undefined
