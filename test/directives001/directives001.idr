module directives001

%access export


data Foo = MkFoo String

%deprecate Foo "To be replaced with `Bar`."

data Bar : Type where
    MkBar : Nat -> Nat -> Bar


mkFoo : String -> Foo
mkFoo = MkFoo

%deprecate mkFoo "To be replaced with `mkBar`."

mkBar : Nat -> Bar
mkBar a = MkBar a a

%fragile mkBar "How `Bar`s are to be created is still being discussed, `mkBar` is subject to change."

namespace Main
  main : IO ()
  main = do
    let b = mkBar 1
    putStrLn $ "Hello World"
