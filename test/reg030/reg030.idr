import Control.Isomorphism

class Set univ where
  member : univ -> univ -> Type

isSubsetOf : Set univ => univ -> univ -> Type
isSubsetOf {univ} a b = (c : univ) -> (member c a) -> (member c b)

class Set univ => HasPower univ where
  Powerset : (a : univ) -> 
             Exists univ (\Pa => (c : univ) -> 
                                 (isSubsetOf c a) -> member c Pa)

powerset : HasPower univ => univ -> univ
powerset {univ} a = getWitness (Powerset a)
