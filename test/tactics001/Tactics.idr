module Tactics

import Language.Reflection.Elab

import Data.Vect

%language ElabReflection
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
  %runElab (do compute
               rewriteWith `(sym $ plusZeroRightNeutralNew ~(Var `{k}))
               fill $ refl `(Nat : Type) `(S ~(Var `{k}))
               solve)

plusSuccRightSuccNew : (j, k : Nat) -> plus j (S k) = S (plus j k)
plusSuccRightSuccNew Z k = Refl
plusSuccRightSuccNew (S j) k =
  %runElab (do compute
               rewriteWith `(sym $ plusSuccRightSuccNew ~(Var `{j}) ~(Var `{k}))
               fill $ refl `(Nat : Type) `(S (S (plus ~(Var `{j}) ~(Var `{k}))))
               solve)

-- Test that side effects in new tactics work

mkDecl : ()
mkDecl = %runElab (do declareType $ Declare (NS (UN "repUnit") ["Tactics"])
                                               [MkFunArg (UN "z") `(Nat) Implicit NotErased]
                                               `(Vect ~(Var (UN "z")) ())
                      fill `(() : ())
                      solve)

repUnit = pure ()
