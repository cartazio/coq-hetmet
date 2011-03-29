{-# OPTIONS_GHC -XModalTypes -ddump-types -XNoMonoPatBinds #-}
module LambdaCalculusInterpreter
where
import Prelude hiding ( id, (.) )

-- 
-- A two-stage (untyped) Lambda Calculus interpreter, from Hughes'
-- __Generalizing Monads to Arrows__.
--

--
-- Note how we have to use environment classifiers to tie Env, Val,
-- and Exp together (I miss Coq's [Section] command!!), yet the result
-- of "eval" is polymorphic in this classifier -- so long as the "Env"
-- and "Val" share it.
-- 

type Id    = String
data Exp   = Var Id
           | Add Exp Exp 
           | If  Exp Exp Exp
           | App Exp Exp 
           | Lam Id  Exp

type Env c = [(Id,Val c)]
data Val c = Num Int | Fun <[Val c -> Val c]>@c


--
-- This won't work until I implement proper support for inductive
-- types in the guest language
--

{-
eval :: Exp -> forall c. <[ Env c -> Val c ]>@c

eval (If  e1 e2 e3) = <[ \env -> if   ~~(eval e1)
                                 then ~~(eval e2)
                                 else ~~(eval e3) ]>

eval (Add e1 e2)    = <[ \env -> let    (Num v1) = ~~(eval e1) env
                                 in let (Num v2) = ~~(eval e2) env
                                 in     (Num (v1+v2))         ]>

eval (Lam x e)      = <[ \env -> Fun (\v -> ~~(eval e) ((x,v):env)) ]>

eval (App e1 e2)    = <[ \env -> case ~~(eval e1) env of
                                   Fun f -> f ~~(eval e2) env ]>
-}
