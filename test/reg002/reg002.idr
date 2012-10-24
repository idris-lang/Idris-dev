module Main

%default total

data CoNat 
    = Co Nat
    | Infinity

S : CoNat -> CoNat
S (Co n)   = Co (S n)
S Infinity = Infinity

Sn_notzero : Main.S n = Co 0 -> _|_
Sn_notzero = believe_me 

S_Co_not_Inf : S (Co n) = Infinity -> _|_
S_Co_not_Inf = believe_me

S_inj : (n : CoNat) -> (m : CoNat) -> S n = S m -> n = m
S_inj (Co n)   (Co _)   refl = refl
S_inj (Co n)   Infinity p    = FalseElim (S_Co_not_Inf p)
S_inj Infinity (Co m)   p    = FalseElim (S_Co_not_Inf (sym p))
S_inj Infinity Infinity refl = refl

swap : {n : Nat} -> Vect A n -> Vect A n
swap Nil            = Nil
swap (x :: Nil)     = x :: Nil
swap (x :: y :: xs) = (y :: x :: (swap xs))

main : IO ()
main = print (swap [1,2,3,4,5])
