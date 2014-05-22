module Prelude.Pairs

%access public
%default total

||| Dependent pair where the first field is erased.
data Exists : {a : Type} -> (P : a -> Type) -> Type where
    witness : .{x : a} -> (pf : P x) -> Exists P

||| Dependent pair where the second field is erased. 
data Subset : (a : Type) -> (P : a -> Type) -> Type where
    element : (x : a) -> .(pf : P x) -> Subset a P

||| Class of dependent pair constructors.
class DependentPair f where
    ||| Project the first field from a dependent pair.
    getWitness : f a P -> a

    ||| Project the second field from a dependent pair.
    getProof : (x : f a P) -> P (getWitness x)

instance DependentPair Pair where
    getWitness (pair x pf) = x
    getProof   (pair x pf) = pf

instance DependentPair Exists where
    getWitness (witness x pf) = x
    getProof   (witness x pf) = pf

instance DependentPair Subset where
    getWitness (element x pf) = x
    getProof   (element x pf) = pf
