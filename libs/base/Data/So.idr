module Data.So

%default total
%access public export

||| Ensure that some run-time Boolean test has been performed.
|||
||| This lifts a Boolean predicate to the type level. See the function `choose`
||| if you need to perform a Boolean test and convince the type checker of this
||| fact.
|||
||| If you find yourself using `So` for something other than primitive types,
||| it may be appropriate to define a type of evidence for the property that you
||| care about instead.
data So : Bool -> Type where
  Oh : So True

implementation Uninhabited (So False) where
  uninhabited Oh impossible

||| Perform a case analysis on a Boolean, providing clients with a `So` proof
choose : (b : Bool) -> Either (So b) (So (not b))
choose True  = Left Oh
choose False = Right Oh

--------------------------------------------------------------------------------
-- Absurd- and negation-related properties
--------------------------------------------------------------------------------

||| Absurd when you have proof that both `b` and `not b` is true.
export
soAbsurd : So b -> So (not b) -> Void
soAbsurd Oh = uninhabited

||| Absurd when you have a proof of both `b` and `not b` (with something else).
export
soConjAbsurd : So b -> So (not b && c) -> Void
soConjAbsurd Oh = uninhabited

||| Transmission between usage of value-level `not` and type-level `Not`.
export
soNotToNotSo : So (not b) -> Not (So b)
soNotToNotSo = flip soAbsurd

--------------------------------------------------------------------------------
--- Operations for `So` of conjunction
--------------------------------------------------------------------------------

||| Given proofs of two properties you have a proof of a conjunction.
export
(&&) : So b -> So c -> So (b && c)
Oh && Oh = Oh

||| A proof of the right side of a conjunction given a proof of the left side.
export
takeSoConjPart : So b -> So (b && c) -> So c
takeSoConjPart Oh Oh = Oh

||| Splits the proof of a conjunction to a pair of proofs for each part.
export
splitSoConj : So (b && c) -> (So b, So c)
splitSoConj {b=True} Oh = (Oh, Oh)
