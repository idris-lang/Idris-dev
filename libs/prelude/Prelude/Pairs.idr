module Prelude.Pairs

import Builtins

%access public export
%default total

swap : (a, b) -> (b, a)
swap (x, y) = (y, x)

using (a : Type, P : a -> Type)

  ||| Dependent pair where the first field is erased.
  data Exists : (P : a -> Type) -> Type where
    Evidence : .(x : a) -> (pf : P x) -> Exists P

  ||| Dependent pair where the second field is erased.
  data Subset : (a : Type) -> (P : a -> Type) -> Type where
    Element : (x : a) -> .(pf : P x) -> Subset a P

  -- Monomorphic projections

  namespace Exists
    getWitness : Exists {a} P -> a
    getWitness (Evidence x pf) = x

    getProof : (x : Exists {a} P) -> P (getWitness x)
    getProof (Evidence x pf) = pf

  namespace Subset
    getWitness : Subset a P -> a
    getWitness (Element x pf) = x

    getProof : (x : Subset a P) -> P (getWitness x)
    getProof (Element x pf) = pf

  namespace DPair
    fst : DPair a P -> a
    fst (x ** pf) = x

    snd : (x : DPair a P) -> P (fst x)
    snd (x ** pf) = pf

    getWitness : DPair a P -> a
    getWitness = fst
    %deprecate DPair.getWitness "This is being deprecated in favour of `fst`."

    getProof : (x : DPair a P) -> P (fst x)
    getProof = snd
    %deprecate DPair.getProof "This is being deprecated in favour of `snd`."

  -- Polymorphic (interface-based) projections have been removed
  -- because type-directed name disambiguation works better.
