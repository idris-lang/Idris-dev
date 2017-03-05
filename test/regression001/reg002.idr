mutual
  interface MyInterface a where
    foo : a -> b
    foo = bar

  bar : MyInterface a => a -> b
  bar = ?bar_rhs

