%default total

MkThing : Bool -> Type
MkThing True = Nat
MkThing False = Bool

testCov : (x : Bool) -> MkThing x -> Nat
testCov False False = ?testCov_rhs_3
testCov False True = ?testCov_rhs_4

testCov' : (x : Bool ** MkThing x) -> Nat
testCov' (False ** False) = ?testCov_rhs_3
testCov' (False ** True) = ?testCov_rhs_4

