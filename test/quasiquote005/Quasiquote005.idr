module Quasiquote005

-- Test Raw quasiquotes

test : the Language.Reflection.Raw `(plus (S Z) (S Z)) =
       RApp (RApp (Var (NS (UN "plus") ["Nat", "Prelude"]))
                  (RApp (Var (NS (UN "S") ["Nat", "Prelude"]))
                        (Var (NS (UN "Z") ["Nat", "Prelude"]))))
            (RApp (Var (NS (UN "S") ["Nat", "Prelude"]))
                  (Var (NS (UN "Z") ["Nat", "Prelude"])))
test = Refl

firstAddend : Raw -> Maybe Raw
firstAddend `(plus ~first ~_) = Just first
firstAddend _ = Nothing

firstAddendOk : firstAddend (RApp (RApp (Var (NS (UN "plus") ["Nat", "Prelude"]))
                                        (RApp (Var (NS (UN "S") ["Nat", "Prelude"]))
                                              (Var (NS (UN "Z") ["Nat", "Prelude"]))))
                                  (Var (NS (UN "Z") ["Nat", "Prelude"]))) =
                the (Maybe Raw) (Just `(S Z))
firstAddendOk = Refl
