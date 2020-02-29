||| Properties of factorial functions.
module Data.Nat.Fact

%access public export

%default total

||| Recursive definition of factorial.
factRec : Nat -> Nat
factRec Z = 1
factRec (S k) = (S k) * factRec k

||| Tail-recursive accumulator for factItr.
factAcc : Nat -> Nat -> Nat
factAcc Z acc = acc
factAcc (S k) acc = factAcc k $ (S k) * acc

||| Iterative definition of factorial.
factItr : Nat -> Nat
factItr n = factAcc n 1

----------------------------------------

||| Multiplicand-shuffling lemma.
multShuffle : (a, b, c : Nat) -> a * (b * c) = b * (a * c)
multShuffle a b c =
  rewrite multAssociative a b c in
    rewrite multCommutative a b in
      sym $ multAssociative b a c

||| Multiplication of the accumulator.
factAccMult : (a, b, c : Nat) ->
  a * factAcc b c = factAcc b (a * c)
factAccMult _ Z _ = Refl
factAccMult a (S k) c =
  rewrite factAccMult a k (S k * c) in
    rewrite multShuffle a (S k) c in
      Refl

||| Addition of accumulators.
factAccPlus : (a, b, c : Nat) ->
  factAcc a b + factAcc a c = factAcc a (b + c)
factAccPlus Z _ _ = Refl
factAccPlus (S k) b c =
  rewrite factAccPlus k (S k * b) (S k * c) in
    rewrite sym $ multDistributesOverPlusRight (S k) b c in
      Refl

||| The recursive and iterative definitions are the equivalent.
factRecItr : (n : Nat) -> factRec n = factItr n
factRecItr Z = Refl
factRecItr (S k) =
  rewrite factRecItr k in
    rewrite factAccMult k k 1 in
      rewrite multOneRightNeutral k in
        factAccPlus k 1 k
