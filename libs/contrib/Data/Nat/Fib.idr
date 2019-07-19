||| Properties of the Fibonacci function.
module Data.Nat.Fib

%access public export

%default total

||| Recursive definition of Fibonacci.
fibRec : Nat -> Nat
fibRec Z = Z
fibRec (S Z) = S Z
fibRec (S (S k)) = fibRec (S k) + fibRec k

||| Accumulator for fibItr.
fibAcc : Nat -> Nat -> Nat -> Nat
fibAcc Z a _ = a
fibAcc (S k) a b = fibAcc k b (a + b)

||| Iterative definition of Fibonacci.
fibItr : Nat -> Nat
fibItr n = fibAcc n 0 1

||| Addend shuffling lemma.
plusLemma : (a, b, c, d : Nat) -> (a + b) + (c + d) = (a + c) + (b + d)
plusLemma a b c d =
  rewrite sym $ plusAssociative a b (c + d) in
    rewrite plusAssociative b c d in
      rewrite plusCommutative b c in
        rewrite sym $ plusAssociative c b d in
          plusAssociative a c (b + d)

||| Helper lemma for fibacc.
fibAdd : (n, a, b, c, d : Nat) ->
  fibAcc n a b + fibAcc n c d = fibAcc n (a + c) (b + d)
fibAdd Z _ _ _ _ = Refl
fibAdd (S Z) _ _ _ _ = Refl
fibAdd (S (S k)) a b c d =
  rewrite fibAdd k (a + b) (b + (a + b)) (c + d) (d + (c + d)) in
    rewrite plusLemma b (a + b) d (c + d) in
      rewrite plusLemma a b c d in
        Refl

||| Iterative and recursive Fibonacci definitions are equivalent.
fibEq : (n : Nat) -> fibRec n = fibItr n
fibEq Z = Refl
fibEq (S Z) = Refl
fibEq (S (S k)) =
  rewrite fibEq k in
    rewrite fibEq (S k) in
      fibAdd k 1 1 0 1
