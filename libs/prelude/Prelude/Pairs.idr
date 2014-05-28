module Prelude.Pairs

import Builtins

%access public
%default total

using (a : Type, P : a -> Type)

    ||| Dependent pair where the first field is erased.
    data Exists : (P : a -> Type) -> Type where
        evidence : .(x : a) -> (pf : P x) -> Exists P

    ||| Dependent pair where the second field is erased. 
    data Subset : (a : Type) -> (P : a -> Type) -> Type where
        element : (x : a) -> .(pf : P x) -> Subset a P

    ||| The type class of dependent pairs.
    class DepPair (a : Type) (P : a -> Type) (T : Type) where

        ||| The first projection from a dependent pair.
        getWitness : (x : T) -> a

        ||| The second projection from a dependent pair.
        getProof : (x : T) -> P (getWitness x)

    instance DepPair a P (Exists {a} P) where
        getWitness (evidence x pf) = x
        getProof   (evidence x pf) = pf

    instance DepPair a P (Subset a P) where
        getWitness (element x pf) = x
        getProof   (element x pf) = pf

    instance DepPair a P (Pair a P) where
        getWitness (pair x pf) = x
        getProof   (pair x pf) = pf
