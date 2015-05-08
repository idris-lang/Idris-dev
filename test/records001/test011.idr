module Main

import Data.Vect

record Foo (n : Nat) where
  constructor MkFoo
  name : String
  things : Vect n a
  more_things : Vect m b
  
record Person where
  constructor MkPerson
  name : String
  age : Int

testFoo : Foo 3
testFoo = MkFoo "name" [1,2,3] [4,5,6,7]

person : Person
person = MkPerson "Fred" 30

main : IO ()
main = do let x = record { name = "foo",
                           more_things = reverse ["a","b"] } testFoo
          printLn $ name x
          printLn $ name person
          printLn $ things x
          printLn $ more_things x
          printLn $ age (record { age = 25 } person)

