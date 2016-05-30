data Con2 : Type where
     MkCon2 : (a : Type) -> Con2 = a -> (a -> Void) -> Con2
  
total
runCon2 : Con2 -> (Con2 -> Void)
runCon2 (MkCon2 _ Refl f) = f

