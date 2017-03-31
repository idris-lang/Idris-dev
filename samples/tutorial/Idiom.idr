module idiom

data Expr = Var String
          | Val Int
          | Add Expr Expr

data Eval : Type -> Type where
   MkEval : (List (String, Int) -> Maybe a) -> Eval a

fetch : String -> Eval Int
fetch x = MkEval fetchVal where
    fetchVal : List (String, Int) -> Maybe Int
    fetchVal [] = Nothing
    fetchVal ((v, val) :: xs) = if (x == v) then (Just val) else (fetchVal xs)

implementation Functor Eval where
    map f (MkEval g) = MkEval (\e => map f (g e))

implementation Applicative Eval where
    pure x = MkEval (\e => Just x)

    (<*>) (MkEval f) (MkEval g) = MkEval (\x => app (f x) (g x)) where
       app : Maybe (a -> b) -> Maybe a -> Maybe b
       app (Just fx) (Just gx) = Just (fx gx)
       app _         _         = Nothing

eval : Expr -> Eval Int
eval (Var x)   = fetch x
eval (Val x)   = [| x |]
eval (Add x y) = [| eval x + eval y |]

runEval : List (String, Int) -> Expr -> Maybe Int
runEval env e = case eval e of
    MkEval envFn => envFn env

m_add' : Maybe Int -> Maybe Int -> Maybe Int
m_add' x y = [| x + y |]

