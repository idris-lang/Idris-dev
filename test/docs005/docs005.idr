module docs005

import Data.List

%default total

||| A foobar with an auto implicit
data Foobar : Type where
  ||| New Foo
  |||
  ||| @xs Some `xs`
  ||| @ys Some `ys`
  ||| @prf The prf
  ||| @prf1 A prf
  NewFoo : (xs : List String)
        -> (ys : List Nat)
        -> {prf1 : NonEmpty xs}
        -> {auto prf : NonEmpty ys}
        -> Foobar
