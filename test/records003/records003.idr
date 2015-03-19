record Person (age : Nat) where
  constructor MkPerson
  name : String
  
--set_param_age : (age_in : Nat) -> Person age -> Person age_in
--set_param_age age_in (MkPerson {age=age} name) = MkPerson {age=age_in} name

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

--set_param_year : (year_in : Int) -> Meeting year -> Meeting year_in
--set_param_year year_in (MkMeeting {year=year} event organiser) = MkMeeting {year=year_in} event organiser

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
main = do print (record { event->organiser->name } test)
          print (record { event->organiser->param_age } test)
          print (record { event->organiser->param_age } idm_gbg)
          print (record { organiser->param_age } test)
          print (record { organiser->param_age } idm_gbg)
          print (record { param_year } idm_gbg)

