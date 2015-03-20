record Person (age : Nat) where
  constructor MkPerson
  name : String

record Event where
  constructor MkEvent
  name : String
  organiser : Person a

record Meeting (year : Int) where
  constructor MkMeeting
  event : Event
  organiser : Person a

new_organiser : String -> List (Meeting x) -> List (Meeting x)
new_organiser n = map (record { event->organiser->name = n }) 

next_year : Meeting x -> Meeting (x+1)
next_year m = record { organiser->param_age
                          = record { organiser->param_age } m + 1,
                       event->organiser->param_age
                          = record { event->organiser->param_age } m + 1,
                       param_year = _ } m

fred : Person 20
fred = MkPerson "Fred"

jim : Person 29
jim = MkPerson {age=29} "Jim"

idm : Event
idm = MkEvent "Idris Developers Meeting" fred

idm_gbg : Meeting 2014
idm_gbg = MkMeeting idm jim

test : Meeting 2015
test = next_year idm_gbg

main : IO ()
main = do printLn (record { event->organiser->name } test)
          printLn (record { event->organiser->param_age } test)
          printLn (record { event->organiser->param_age } idm_gbg)
          printLn (record { organiser->param_age } test)
          printLn (record { organiser->param_age } idm_gbg)
          printLn (record { param_year } idm_gbg)
