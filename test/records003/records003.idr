record Person : Nat -> Type where
       MkPerson : (name : String) ->
                  (age : Nat) ->
                  Person age

record Event : Type where
       MkEvent : (name : String) -> (organiser : Person a) -> Event 

record Meeting : Int -> Type where
       MkMeeting : (event : Event) -> 
                   (organiser : Person a) -> 
                   (year : Int) -> 
                   Meeting year

new_organiser : String -> List (Meeting x) -> List (Meeting x)
new_organiser n = map (record { event->organiser->name = n }) 

next_year : Meeting x -> Meeting (x+1)
next_year m = record { organiser->age
                          = record { organiser->age } m + 1,
                       event->organiser->age
                          = record { event->organiser->age } m + 1,
                       year = _ } m

fred : Person 20
fred = MkPerson "Fred" _

jim : Person 29
jim = MkPerson "Jim" 29

idm : Event
idm = MkEvent "Idris Developers Meeting" fred

idm_gbg : Meeting 2014
idm_gbg = MkMeeting idm jim _

test : Meeting 2015
test = next_year idm_gbg

main : IO ()
main = do print (record { event->organiser->name } test)
          print (record { event->organiser->age } test)
          print (record { event->organiser->age } idm_gbg)
          print (record { organiser->age } test)
          print (record { organiser->age } idm_gbg)
          print (record { year } idm_gbg)


