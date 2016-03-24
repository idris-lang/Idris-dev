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


