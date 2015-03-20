module Tactics

import Language.Reflection.Tactical

import Data.Vect


%default total

-- Test that basic proofs with new-style tactics work

||| Construct a Refl at some particular type for some particular term
||| @ t the type
||| @ x the term for equality to be reflexive at
refl : (t, x : Raw) -> Raw
refl t x = RApp (RApp (Var (UN "Refl")) t) x

plusZeroRightNeutralNew : (n : Nat) -> plus n 0 = n
plusZeroRightNeutralNew Z = Refl
plusZeroRightNeutralNew (S k) =
  %runTactics (do rewriteWith `(sym $ plusZeroRightNeutralNew ~(Var "k"))
                  fill $ refl `(Nat : Type) `(S ~(Var (UN "k")))
                  solve)

plusSuccRightSuccNew : (j, k : Nat) -> plus j (S k) = S (plus j k)
plusSuccRightSuccNew Z k = Refl
plusSuccRightSuccNew (S j) k =
  %runTactics (do rewriteWith `(sym $ plusSuccRightSuccNew ~(Var "j") ~(Var (UN "k")))
                  fill $ refl `(Nat : Type) `(S (S (plus ~(Var (UN "j")) ~(Var (UN "k")))))
                  solve)

-- Test that side effects in new tactics work

mkDecl : ()
mkDecl = %runTactics (do declareType $ Declare (NS (UN "repUnit") ["Tactics"])
                                               [Implicit (UN "z") `(Nat)]
                                               `(Vect ~(Var (UN "z")) ())
                         fill `(() : ())
                         solve)

repUnit = pure ()
