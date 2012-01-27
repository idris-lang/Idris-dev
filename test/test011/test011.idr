module main

record Foo : Nat -> Set where
    MkFoo : (name : String) ->
            (things : Vect a n) ->
            (more_things : Vect b m) ->
            Foo n

record Person : Set where
    MkPerson : (name : String) -> (age : Int) -> Person

testFoo : Foo 3
testFoo = MkFoo "name" [1,2,3] [4,5,6,7]

person : Person
person = MkPerson "Fred" 30

main : IO ()
main = do let x = record { name = "foo", 
                           more_things = reverse ["a","b"] } testFoo
          print $ name x
          print $ name person
          print $ things x
          print $ more_things x
          print $ age (record { age = 25 } person)

