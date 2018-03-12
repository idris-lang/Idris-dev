|||
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
||| 0.0 + 0.2
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
|||
||| @brief  This is a simple module for testing
||| @tooltip A testing module.
||| @version 0.0.1
||| @date    1971-01-01
||| @copyright Morgan The Goat 2017
||| @license see LICENSE
||| @stability fairly
||| @portability write once, run everywhere
||| @maintainer Morgan The Goat
||| @author Morgan The Goat
module Test

||| Docs for datatype Test.
|||
||| @brief For testing
||| @tooltip For testing
||| @note This is a test
||| @note This is another test
||| @remark Fancy annotations.
data Test = MkTest

|||
||| @param ty The type.
data Thing : (ty : Type) -> Type where
  MkThing : Thing Nat

|||
||| @ty The old style works still...for now...
data Foobar : (ty : Type) -> Type where
  MkFoo : Foobar String

namespace Main
  |||
  main : IO ()
  main = putStrLn "Hoi!"
