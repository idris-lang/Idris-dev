||| Docs for module Test.
|||
||| It is a great module.
||| Prelude thingy:
||| ```idris example
||| "foo" ++ "bar"
||| ```
|||
||| Imported thingy:
||| ```idris example
||| 0.0 :+ 0.2
||| ```
|||
||| Type error:
||| ```idris
||| "foo" + 2
||| ```
|||
||| From this module:
||| ```idris example
||| MkTest
||| ```
module Test
import Data.Complex

%access public export

myplus : Nat -> Nat -> Nat
myplus Z j = j
myplus (S k) j = S (myplus k j)

||| Docs for datatype Test.
data Test = MkTest

data Thing : Type -> Type where
  MkThing : Thing Nat

-- fnord ++ xyz do done let module argh

namespace Main
  ||| Main is handy to do things in. ++. 
  main : IO ()
  main = do putStrLn "Hi!"
            l <- getLine
            case l of
              "" => putStrLn "No!"
              str => putStrLn str
