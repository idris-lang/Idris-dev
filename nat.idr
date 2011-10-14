data Nat = O | S Nat;

plus : Nat -> Nat -> Nat;
plus O     y = y;
plus (S k) y = S (plus k y);

