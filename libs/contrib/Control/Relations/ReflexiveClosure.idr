||| General definitions and theorems about
||| reflexive closure.
module Relations.ReflexiveClosure
import Basics
import Equivalence

%default total
%access public


||| Take the reflexive closure of a relation
data RC : Rel a -> Rel a where
  RCIncl : rel x y -> RC rel x y
  RCRefl : RC rel x x

rcRefl : {rel : Rel a} -> Reflexive (RC rel)
rcRefl _ = RCRefl

||| The reflexive closure is the coarsest finer reflexive relation.
rcSmallest : {rel, rel' : Rel a} -> rel `Coarser` rel' -> Reflexive rel' ->
             RC rel `Coarser` rel'
rcSmallest {a} rcr' ref' x y (RCIncl xy) = rcr' _ _ xy
rcSmallest {a} rcr' ref' x x RCRefl = ref' x

||| The reflexive closure of a transitive relation is transitive.
rcTransTrans : {rel : Rel a} -> Transitive rel -> Transitive (RC rel)
rcTransTrans trns x y z (RCIncl xy) (RCIncl yz) = RCIncl (trns _ _ _ xy yz)
rcTransTrans trns x z z xz RCRefl = xz
rcTransTrans trns x x z RCRefl xz = xz

||| The reflexive closure of an asymmetric relation is antisymmetric.
rcAsymmetricAntisymmetric : {rel : Rel a} -> Asymmetric rel ->
                            Antisymmetric (RC rel)
rcAsymmetricAntisymmetric asym x y (RCIncl xy) (RCIncl yx) =
  absurd $ asym _ _ xy yx
rcAsymmetricAntisymmetric asym x x RCRefl xx = Refl
rcAsymmetricAntisymmetric asym x x xx RCRefl = Refl

rcInflationary : {a : Type} -> Inflationary (RC {a})
rcInflationary rel x y xy = RCIncl xy

rcIncreasing : {a : Type} -> Increasing (RC {a})
rcIncreasing rel1 rel2 f x y (RCIncl xy) = RCIncl (f x y xy)
rcIncreasing rel1 rel2 f x x RCRefl = RCRefl

rcIdempotent : {a : Type} -> Idempotent (RC {a})
rcIdempotent {a} rel = MkEquivalent yeah that
      where
        yeah : (x : a) -> (y : a) -> RC rel x y -> RC (RC rel) x y
        yeah x y (RCIncl z) = RCIncl (RCIncl z)
        yeah x x RCRefl = RCRefl

        that : (x : a) -> (y : a) -> RC (RC rel) x y -> RC rel x y
        that x y (RCIncl z) = z
        that x x RCRefl = RCRefl

||| Reflexive closure is a closure operator
rcIsClosureOperator : ClosureOperator RC
rcIsClosureOperator = MkClosureOperator rcInflationary rcIncreasing rcIdempotent

