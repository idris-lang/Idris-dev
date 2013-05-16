module wheres

even : Nat -> Bool 
even O = True 
even (S k) = odd k where 
  odd O = False 
  odd (S k) = even k 

test : List Nat
test = [c (S 1), c O, d (S O)]
  where c x = 42 + x
        d y = c (y + 1 + z y)
              where z w = y + w

