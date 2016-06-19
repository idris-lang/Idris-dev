module OTT

mutual

  data U : Type where
    MkU : U
    Zero : U
    One : U
    Two : U
    Pi : (s : U) -> (t : El s -> U) -> U

  El : U -> Type
  El MkU = U
  El Zero = Void
  El One = ()
  El Two = Bool
  El (Pi s t) = (x : El s) -> El (t x)

infixr 10 ~>
(~>) : U -> U -> U
s ~> t = Pi s $ const t

syntax "<|" [s] "|>" = El s
syntax [x] "==" [y] "in" [s] = EQ s x s y

EQ : (s : U) -> <| s |> -> (t : U) -> <| t |> -> U
EQ MkU MkU MkU MkU = One
EQ MkU Zero MkU Zero = One
EQ MkU One MkU One = One
EQ MkU Two MkU Two = One
EQ MkU (Pi s t) MkU (Pi s' t') = assert_total $ Pi s $ \x => Pi s' $ \y => EQ s x s' y ~> EQ MkU (t x) MkU (t' y)
EQ Zero x Zero y = One
EQ One x One y = One
EQ Two True Two True = One
EQ Two False Two False = One
EQ (Pi s t) f (Pi s' t') g = assert_total $ Pi s $ \x => Pi s' $ \y => EQ s x s' y ~> EQ (t x) (f x) (t' y) (g y)
EQ _ _ _ _ = Zero

example : <| (Basics.id == Basics.id in (OTT.Two ~> OTT.Two)) |>
example = ?prf

