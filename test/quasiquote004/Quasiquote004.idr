module Quasiquote004

import Language.Reflection

%default total

normPlus : List (TTName, Binder TT) -> TT -> Tactic
normPlus ctxt `((=) {A = Nat} {B = Nat} ~x ~y) = normPlus ctxt x `Seq` normPlus ctxt y
normPlus ctxt `(S ~n) = normPlus ctxt n
normPlus ctxt `(plus ~n (S ~m)) = Seq (Rewrite `(plusSuccRightSucc ~n ~m))
                                      (normPlus ctxt m)
normPlus _ _ = Skip


zero : List (TTName, Binder TT) -> TT -> Tactic
zero ctxt `(Nat) = Exact `(Z)
zero _ _ = Fail [TextPart "Not a Nat goal"]

-- A number is fizzy if it is evenly divisible by 3
data Fizzy : Nat -> Type where
  ZeroFizzy : Fizzy Z
  Fizz : Fizzy n -> Fizzy (3 + n)

-- Fizzy is a correct specification of divisibility by 3 - that is, if n is
-- fizzy then there exists some k such that n = 3*k.
fizzyCorrect : (n : Nat) -> Fizzy n -> (k : Nat ** n = 3 * k)
fizzyCorrect Z ZeroFizzy = (Z ** Refl)
fizzyCorrect (S (S (S k))) (Fizz x) =
  let (k' ** ih) = fizzyCorrect k x
  in (S k' ** ?fizzyIsAOK)

someNat : Nat
someNat = ?getMeNat

notNat : String
notNat = ?getMeNat'

---------- Proofs ----------
Quasiquote004.getMeNat = proof
  applyTactic zero

Quasiquote004.fizzyIsAOK = proof
  compute
  intros
  applyTactic normPlus
  applyTactic normPlus
  rewrite ih
  trivial

Quasiquote004.getMeNat' = proof
  applyTactic zero
