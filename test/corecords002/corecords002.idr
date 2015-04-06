module Main

corecord Foo (n : Nat) where
  constructor MkFoo
  bar : String
  baz : Foo n
  
corecord Blargh where
  constructor MkBlargh
  num : Nat
  argh : Foo num
  
total  
foo : Foo 7
foo = MkFoo "Foo" foo  

total
blargh : Blargh
blargh = MkBlargh 7 foo
  
main : IO ()
main = do printLn (record { argh->bar } blargh)
          printLn (record { argh->baz->bar } blargh)
          printLn (record { argh->baz->baz->bar } blargh)
