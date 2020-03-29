
[PlusNatSemi] Semigroup Nat where
  (<+>) x y = x + y

  semigroupOpIsAssociative = plusAssociative

[MultNatSemi] Semigroup Nat where
  (<+>) x y = x * y

  semigroupOpIsAssociative = multAssociative

[PlusNatMonoid] Monoid Nat using PlusNatSemi where
  neutral = 0

  monoidNeutralIsNeutralL = plusZeroRightNeutral
  monoidNeutralIsNeutralR = plusZeroLeftNeutral

[MultNatMonoid] Monoid Nat using MultNatSemi where
  neutral = 1

  monoidNeutralIsNeutralL = multOneRightNeutral
  monoidNeutralIsNeutralR = multOneLeftNeutral

test : Monoid a => a -> a
test x = x <+> x <+> neutral

[CmpLess] Ord Int where
  compare x y = if (x == y) then EQ else
                   if (boolOp prim__sltInt x y) then GT else LT

foo : Int -> Int -> Bool
foo x y = x < y

using implementation CmpLess
  foo' : Int -> Int -> Bool
  foo' x y = x < y

using implementation PlusNatMonoid
  main : IO ()
  main = do printLn (test (the Nat 6))
            printLn (test @{MultNatMonoid} 6)

            printLn (foo 3 4)
            printLn (foo' 3 4)
