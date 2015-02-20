module Quasiquote005

test : the Language.Reflection.Raw `(plus (S Z) (S Z)) =
       RApp (RApp (Var (NS (UN "plus") ["Nat", "Prelude"]))
                  (RApp (Var (NS (UN "S") ["Nat", "Prelude"]))
                        (Var (NS (UN "Z") ["Nat", "Prelude"]))))
            (RApp (Var (NS (UN "S") ["Nat", "Prelude"]))
                  (Var (NS (UN "Z") ["Nat", "Prelude"])))
test = Refl
