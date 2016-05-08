
[PlusNatSemi] Semigroup Nat where
  (<+>) x y = x + y

[MultNatSemi] Semigroup Nat where
  (<+>) x y = x * y

[PlusNatMonoid] Monoid Nat using PlusNatSemi where
  neutral = 0

[MultNatMonoid] Monoid Nat using MultNatSemi where
  neutral = 1

test : Monoid a => a -> a
test x = x <+> x <+> neutral

main : IO ()
main = do printLn (test @{PlusNatMonoid} 6)
          printLn (test @{MultNatMonoid} 6)
