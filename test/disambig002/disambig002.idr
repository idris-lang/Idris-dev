import Data.Vect
import Data.Fin
import Control.Isomorphism

-- Tests if Idris can disambiguate between the three `toVect` operators

Dec0 : Type -> Type
Dec0 = Dec

Dec1 : {A : Type} -> (P : A -> Type) -> Type
Dec1 {A} P = (a : A) -> Dec0 (P a)

Unique : Type -> Type
Unique t = (p : t) -> (q : t) -> p = q

Unique0 : Type -> Type
Unique0 = Unique

Unique1 : (t0 -> Type) -> Type
Unique1 {t0} t1 = (v : t0) -> Unique0 (t1 v)

namespace Iso

  from : {A, B : Type} -> Iso A B -> (B -> A)
  from (MkIso to from toFrom fromTo) = from

namespace Fin

  ||| 'Tail' of a finite function
  tail : {A : Type} -> {n : Nat} ->
         (Fin (S n) -> A) -> (Fin n -> A)
  tail f k = f (FS k)

  ||| Maps a finite function to a vector
  toVect : {A : Type} -> {n : Nat} ->
           (Fin n -> A) -> Vect n A
  toVect {n =   Z} _ = Nil
  toVect {n = S m} f = (f FZ) :: (toVect (tail f))

namespace Finite

  ||| Notion of finiteness for types
  Finite : Type -> Type
  Finite A = Exists (\ n => Iso A (Fin n))

  ||| Cardinality of finite types
  card : {A : Type} -> (fA : Finite A) -> Nat
  card = getWitness

  ||| Maps a finite type |A| of cardinality |n| to a vector of |A|-values of length |n|
  toVect : {A : Type} -> (fA : Finite A) -> Vect (card fA) A
  toVect (Evidence n iso) = toVect (from iso)

||| Filters a vector on a decidable property and pairs elements with proofs
filterTag : {A : Type} ->
            {P : A -> Type} ->
            Dec1 P ->
            Vect n A ->
            DPair Nat (\ m => Vect m (DPair A P))
filterTag d1P Nil = (_ ** Nil)
filterTag d1P (a :: as) with (filterTag d1P as)
  | (_ ** tail) with (d1P a)
    | (Yes p) = (_ ** (a ** p) :: tail)
    | (No  _) = (_ ** tail)

||| Maps a finite type |A| and a decidable predicate |P| to a vector |Sigma A P| values
toVect : {A : Type} ->
         {P : A -> Type} ->
         Finite A ->
         Dec1 P ->
         (n : Nat ** Vect n (DPair A P))
toVect fA d1P = filterTag d1P (toVect fA)

sigmaUniqueLemma1 : {A   : Type} ->
                    {P   : A -> Type} ->
                    Unique1 {t0 = A} P ->
                    (a : A) ->
                    (p : P a) ->
                    (ss : Vect n (DPair A P)) ->
                    Elem a (map DPair.fst ss) ->
                    Elem (a ** p) ss

toVectComplete : {A   : Type} ->
                 {P   : A -> Type} ->
                 (fA  : Finite A) ->
                 (d1P : Dec1 P) ->
                 Unique1 {t0 = A} P ->
                 (s   : DPair A P) ->
                 Elem s (snd (toVect fA d1P))
