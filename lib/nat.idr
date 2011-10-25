
data Nat = O | S Nat;

plus : Nat -> Nat -> Nat;
plus O     y = y;
plus (S k) y = S (plus k y);

eqRespS : m = n -> S m = S n;
eqRespS refl = refl;

plusnO : (m : Nat) -> plus m O = m;
plusnO O     = refl;
plusnO (S k) = eqRespS (plusnO k);

