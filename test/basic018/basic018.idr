import Data.Vect

thing : Nat
thing = 42

foo : -- (thing : Nat) ->
      Vect thing elem

bar : {thing : Nat} ->
      Vect thing elem

test : thing = S 41
test = Refl

