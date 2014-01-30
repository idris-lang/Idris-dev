module Main

import Effect.State
import Effect.Exception
import Effect.Random
import Effect.StdIO

data Expr = Var String
          | Val Integer
          | Add Expr Expr
          | Random Integer

Env : Type
Env = List (String, Integer)

-- Evaluator : Type -> Type
-- Evaluator t
--    = Eff m [EXCEPTION String, RND, STATE Env] t

eval : Expr -> Eff IO [EXCEPTION String, STDIO, RND, STATE Env] Integer
eval (Var x) = do vs <- get
                  case lookup x vs of
                        Nothing => raise ("No such variable " ++ x)
                        Just val => return val
eval (Val x) = return x
eval (Add l r) = [| eval l + eval r |]
eval (Random upper) = do val <- rndInt 0 upper
                         putStrLn (show val)
                         return val

testExpr : Expr
testExpr = Add (Add (Var "foo") (Val 42)) (Random 100)

runEval : List (String, Integer) -> Expr -> IO Integer
runEval args expr = run [(), (), 123456, args] (eval expr)

main : IO ()
main = do let x = 42
          val <- runEval [("foo", x)] testExpr
          putStrLn $ "Answer: " ++ show val


