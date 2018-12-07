module WithPatsNoWith

foo : Int -> Bool
foo 1 | 2 | 3 = True
foo _ = False

foo2: Int -> Bool
foo2 n with (succ n)
  foo2 n | 1 | 2 = True
  foo2 _ | _ = False

foo3: Int -> Int -> Bool
foo3 n m with (succ n)
  foo3 _ m | 2 with (succ m)
    foo3 _ _ | 2 | 3 | 4 = True
    foo3 _ _ | 2 | _     = False
  foo3 _ _ | _ = True
