||| Implicit conversions for erased dependent pairs.
module Data.Pairs.Implicit

%access public export
%default total

||| Convert an Evidence to its proof.
implicit evidence : (x : Exists p) -> p (getWitness x)
evidence = getProof

||| Convert an Element to its value (a.k.a. witness).
implicit element : Subset a p -> a
element = getWitness
