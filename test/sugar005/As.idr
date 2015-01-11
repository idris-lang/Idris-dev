module As

-- Test @
isS : Nat -> Maybe Nat
isS Z = Nothing
isS n@(S _) = Just n

-- Test @ under a constructor
hasS : List Nat -> Maybe Nat
hasS (Z::xs) = hasS xs
hasS (n@(S_)::xs) = Just n
hasS _ = Nothing

-- Test nested @s
isSS : Nat -> Maybe (Nat, Nat)
isSS n@(S m@(S _)) = Just (n,m)
isSS _ = Nothing

namespace Main
  main : IO ()
  main = do print $ isS 0
            print $ isS 1
            print $ hasS [0,0,0]
            print $ hasS [0,1,2]
            print $ isSS 5
            print $ isSS 0

