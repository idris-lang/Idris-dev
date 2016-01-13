module Main

data Expr = Var String
          | Val Int
          | Add Expr Expr

data Eval : Type -> Type where
   MkEval : (List (String, Int) -> Maybe a) -> Eval a

fetch : String -> Eval Int
fetch x = MkEval (\e => fetchVal e) where
    fetchVal : List (String, Int) -> Maybe Int
    fetchVal [] = Nothing
    fetchVal ((v, val) :: xs) = if (x == v) then (Just val) else (fetchVal xs)

implementation Functor Eval where
    map f (MkEval g) = MkEval (\e => map f (g e))

implementation Applicative Eval where
    pure x = MkEval (\e => Just x)

    (<*>) (MkEval f) (MkEval g) = MkEval (\x => appAux (f x) (g x)) where
       appAux : Maybe (a -> b) -> Maybe a -> Maybe b
       appAux (Just fx) (Just gx) = Just (fx gx)
       appAux _         _         = Nothing

eval : Expr -> Eval Int
eval (Var x)   = fetch x
eval (Val x)   = [| x |]
eval (Add x y) = [| eval x + eval y |]

runEval : List (String, Int) -> Expr -> Maybe Int
runEval env e with (eval e) {
    | MkEval envFn = envFn env
}

main : IO ()
main = do printLn [| (\x => x *2) (Just 4) |]
          printLn [| plus (Just 4) (Just 5) |]
          printLn (runEval [("x",21), ("y", 20)] (Add (Val 1) (Add (Var "x") (Var "y"))))
          printLn (runEval [("x",21)] (Add (Val 1) (Add (Var "x") (Var "y"))))
