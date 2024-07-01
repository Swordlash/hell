module Language.Hell.Evaluate where

import Language.Hell.Term
import Language.Hell.Var

--------------------------------------------------------------------------------
-- Evaluator
--

-- This is the entire evaluator. Type-safe and total.
eval :: env -> Term env t -> t
eval env (Var v) = lookp v env
eval env (Lam _ e) = \x -> eval (env, x) e
eval env (App e1 e2) = eval env e1 (eval env e2)
eval _ (Lit a) = a
