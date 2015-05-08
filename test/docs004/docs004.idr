module Main

||| Some record Foo
||| @a a type
record Foo a where
  ||| Constructor for Foo
  constructor MkFoo
  ||| A field bar
  bar : Nat
  ||| A field baz
  baz : Bool
