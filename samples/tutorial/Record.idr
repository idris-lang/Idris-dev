import Data.Vect

record Person where
    constructor MkPerson
    firstName, middleName, lastName : String
    age : Int

fred : Person
fred = MkPerson "Fred" "Joe" "Bloggs" 30

record Class where
    constructor ClassInfo
    students : Vect n Person
    className : String

addStudent : Person -> Class -> Class
addStudent p c = record { students = p :: students c } c

addStudent' : Person -> Class -> Class
addStudent' p c = record { students $= (p ::) } c

