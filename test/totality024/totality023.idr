%default total

mutual
  ana : (a -> Maybe a) -> a -> Nat
  ana f = go . f
    where go Nothing  = Z
          go (Just x) = S $ ana f x
