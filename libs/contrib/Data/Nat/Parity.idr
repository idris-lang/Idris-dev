module Data.Nat.Parity

%access public export

--------------------------------------------------------------------------------
-- Parity
--------------------------------------------------------------------------------

mutual
  even : Nat -> Bool
  even Z = True
  even (S k) = odd k

  odd : Nat -> Bool
  odd Z = False
  odd (S k) = even k
