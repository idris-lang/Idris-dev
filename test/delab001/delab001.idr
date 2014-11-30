module Case

foo : Nat -> String
foo n = case n of
          Z => "z"
          S _ => "s"

bar : Nat -> String -> String
bar x y = case x of
            Z => y
            S _ => y ++ y

append : List a -> List a -> List a
append xs ys = case xs of
                 Nil => ys
                 (x :: xs) => x :: append xs ys
