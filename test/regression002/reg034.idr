module main
import Prelude.List

bar : (xs : List ()) -> (ys : List ()) -> 
      Prelude.List.length xs = Prelude.List.length ys -> xs = ys
bar xs xs Refl = Refl

foo : (f : Nat -> Nat) -> (x : Nat) -> (y : Nat) -> f x = f y -> x = y
foo f x x Refl = Refl

