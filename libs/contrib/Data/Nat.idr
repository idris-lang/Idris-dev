module Data.Nat

%default total

diff : Nat -> Nat -> Nat
diff k Z = k
diff Z j = j
diff (S k) (S j) = diff k j
