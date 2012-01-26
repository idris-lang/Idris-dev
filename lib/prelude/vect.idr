module prelude.vect

import prelude.nat
import prelude.fin

%access public

infixr 7 :: 

data Vect : Set -> Nat -> Set where
    Nil   : Vect a O
    (::)  : a -> Vect a k -> Vect a (S k) 

tail : Vect a (S n) -> Vect a n
tail (x :: xs) = xs

lookup : Fin n -> Vect a n -> a
lookup fO     (x :: xs) = x
lookup (fS k) (x :: xs) = lookup k xs
lookup fO      [] impossible
lookup (fS _)  [] impossible
 
app : Vect a n -> Vect a m -> Vect a (n + m)
app []        ys = ys
app (x :: xs) ys = x :: app xs ys

filter : (a -> Bool) -> Vect a n -> (p ** Vect a p)
filter p [] = ( _ ** [] )
filter p (x :: xs) 
    = let (_ ** xs') = filter p xs in
          if (p x) then ( _ ** x :: xs' ) else ( _ ** xs' )

map : (a -> b) -> Vect a n -> Vect b n
map f [] = []
map f (x :: xs) = f x :: map f xs

reverse : Vect a n -> Vect a n
reverse xs = revAcc [] xs where
  revAcc : Vect a n -> Vect a m -> Vect a (n + m)
  revAcc acc []        ?= acc
  revAcc acc (x :: xs) ?= revAcc (x :: acc) xs

---------- Proofs ----------

revAcc_lemma_2 = proof {
    intros;
    rewrite plusSuccRightSucc n k;
    exact value;
}

revAcc_lemma_1 = proof {
    intros;
    rewrite sym (plusZeroRightNeutral n);
    exact value;
}

