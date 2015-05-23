||| General definitions and theorems about
||| reflexive closure.
module Control.Relations.ReflexiveClosure
import Control.Relations.Basics
import Control.Relations.ClosureOperators

%default total
%access public

||| Take the reflexive closure of a relation
data RC : (eq : Rel a) -> Rel a -> Rel a where
  RCIncl : rel x y -> RC eq rel x y
  RCRefl : eq x y -> RC eq rel x y

||| The reflexive closure is the coarsest finer reflexive relation.
rcCoarsest : {rel, rel' : Rel a} -> rel `Coarser` rel' -> Reflexive eq rel' ->
             RC eq rel `Coarser` rel'
rcCoarsest {a} rcr' ref' x y (RCIncl xRELy) = rcr' _ _ xRELy
rcCoarsest {a} rcr' ref' x y (RCRefl xEQy) = ref' x y xEQy

||| The reflexive closure of a transitive relation is transitive.
rcTransTrans : {rel : Rel a} -> (eqEquiv : Equivalence eq) -> (rel `Respects2` eq) ->
               Transitive rel -> Transitive (RC eq rel)
rcTransTrans _ relRespEq trns x y z (RCIncl xy) (RCIncl yz) = RCIncl (trns _ _ _ xy yz)
rcTransTrans _ (f,g) trns x y z (RCIncl xRy) (RCRefl yEz) = RCIncl (f _ _ _ yEz xRy)
rcTransTrans eqEquiv (f,g) trns x y z (RCRefl xEy) (RCIncl yRz) =
  let yEx = getSymmetric eqEquiv x y xEy
  in RCIncl (g _ _ _ yEx yRz)
rcTransTrans eqEquiv relRespEq trns x y z (RCRefl xy) (RCRefl yz) =
  RCRefl (getTransitive eqEquiv x y z xy yz)


||| The reflexive closure of an asymmetric relation is antisymmetric.
rcAsymmetricAntisymmetric : {rel : Rel a} -> rel `Respects2` eq ->
                            Asymmetric rel -> Antisymmetric eq (RC eq rel)
rcAsymmetricAntisymmetric relRespEq asym x y (RCIncl xy) (RCIncl yx) =
  absurd $ asym _ _ xy yx
rcAsymmetricAntisymmetric relRespEq asym x y (RCRefl xy) yx  = xy
rcAsymmetricAntisymmetric (f,g) asym x y (RCIncl xRy) (RCRefl yEx)  =
  let xRx = f _ _ _ yEx xRy
  in absurd $ asym x x xRx xRx

rcInflationary : Inflationary (RC eq)
rcInflationary {eq} rel x y xy = RCIncl xy

rcIncreasing : Increasing (RC eq)
rcIncreasing rel1 rel2 f x y (RCIncl xy) = RCIncl (f x y xy)
rcIncreasing rel1 rel2 f x y (RCRefl xEQy) = RCRefl xEQy

rcIdempotent : {a:Type} -> Idempotent (RC {a} eq)
rcIdempotent {a} {eq} rel = MkEquivalent yeah that
      where
        that : (x : a) -> (y : a) -> RC eq (RC eq rel) x y -> RC eq rel x y
        that x y (RCIncl z) = z
        that x y (RCRefl xEQy) = RCRefl xEQy

        yeah : (x : a) -> (y : a) -> RC eq rel x y -> RC eq (RC eq rel) x y
        yeah x y (RCIncl z) = RCIncl (RCIncl z)
        yeah x y (RCRefl xEQy) = RCIncl (RCRefl xEQy)


||| Reflexive closure is a closure operator
rcIsClosureOperator : ClosureOperator (RC eq)
rcIsClosureOperator = MkClosureOperator rcInflationary rcIncreasing rcIdempotent
