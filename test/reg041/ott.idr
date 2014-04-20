module OTT

mutual

  data U : Type where
    u : U
    zero : U
    one : U
    two : U
    pi : (s : U) -> (t : El s -> U) -> U

  El : U -> Type
  El u = U
  El zero = _|_
  El one = ()
  El two = Bool
  El (pi s t) = (x : El s) -> El (t x)

infixr 10 ~>
(~>) : U -> U -> U
s ~> t = pi s $ const t

syntax "<|" [s] "|>" = El s
syntax [x] "==" [y] "in" [s] = EQ s x s y

%assert_total
EQ : (s : U) -> <| s |> -> (t : U) -> <| t |> -> U
EQ u u u u = one
EQ u zero u zero = one
EQ u one u one = one
EQ u two u two = one
EQ u (pi s t) u (pi s' t') = pi s $ \x => pi s' $ \y => EQ s x s' y ~> EQ u (t x) u (t' y)
EQ zero x zero y = one
EQ one x one y = one
EQ two True two True = one
EQ two False two False = one
EQ (pi s t) f (pi s' t') g = pi s $ \x => pi s' $ \y => EQ s x s' y ~> EQ (t x) (f x) (t' y) (g y)
EQ _ _ _ _ = zero

example : <| id == id in (two ~> two) |>
example = ?prf

