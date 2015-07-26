-- Test for multiple field declarations on one line with the same type

record Person where
  constructor MkPerson
  firstName, middleName, lastName : String

fred : Person
fred = MkPerson "Fred" "Joe" "Bloggs"

main : IO ()
main = do printLn (firstName fred)
          printLn (middleName fred)
          printLn (lastName fred)
