mutual
  total -- should fail due to nonsense in mtot 
  foo : (a -> a -> Ordering) -> 
        a -> List a -> a -> List a -> Ordering -> List a
  foo order x xs y ys _ = mtot order (x :: xs) ys

  total
  mtot : (a -> a -> Ordering) -> List a -> List a -> List a
  mtot order []      right   = right
  mtot order left    []      = left
  mtot order (x::xs) (y::ys) =
      case order x y of
           LT => x :: mtot order xs (y::ys)
           EQ => foo order x xs y (y :: ys) EQ -- throw in some nonsense
           _ => y :: mtot order (x::xs) ys


