module Main

import Data.Floats
import Effect.State
import Data.Fin
import Data.Vect
import Data.Vect.Quantifiers
import Decidable.Equality

record Foo : Nat -> Type where
    MkFoo : (name : String) ->
            (things : Vect n a) ->
            (more_things : Vect m b) ->
            Foo n

record Person : Type where
    MkPerson : (name : String) -> (age : Int) -> Person

testFoo : Foo 3
testFoo = MkFoo "name" [1,2,3] [4,5,6,7]

person : Person
person = MkPerson "Fred" 30

test_index : Integer
test_index = index 0 $ things testFoo

nums : Vect 5 Nat
nums = [4,5,6,7,8]

sum: Fin (length planets) -> Nat -> Nat
sum i v = if (i ~=~ length planets)
                        then v
                        else offsetMomentum (S i) $ (p + v)

main : IO ()
main = do let xF = record { name = "foo",
                           more_things = reverse ["a","b"] } testFoo
          printLn $ name xF
          printLn $ name person
          printLn $ things xF
          printLn $ "| \n | \n v"
          printLn $ test_index
          printLn $ more_things xF
          printLn $ age (record { age = 25 } person)          

