module WithPatsNoWith

foo : Int -> Bool
foo 1 | 2 | 3 = True
foo _ = False

