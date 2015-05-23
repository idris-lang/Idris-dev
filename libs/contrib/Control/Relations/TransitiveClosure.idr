||| General definitions and theorems about relations
module Control.Relations.TransitiveClosure
import Control.Relations.Basics
import Control.Relations.ClosureOperators

%default total
%access public

||| Take the transitive closure of a relation
data TC : Rel a -> Rel a where
  TCIncl : rel x y -> TC rel x y
  TCTrans : {y : a} -> TC rel x y -> TC rel y z -> TC rel x z

||| The transitive closure of a relation is transitive.
tcTransitive : {rel : Rel a} -> Transitive (TC rel)
tcTransitive = (\_, _, _, xRy, yRz => TCTrans xRy yRz)

||| The transitive closure of a relation is the coarsest finer
||| transitive relation.
tcCoarsest : {rel, rel' : Rel a} -> rel `Coarser` rel' -> Transitive rel' ->
             TC rel `Coarser` rel'
tcCoarsest rsubr' tr' x y (TCIncl xy) = rsubr' _ _ xy
tcCoarsest rsubr' tr' x z (TCTrans {y} xy yz) =
  let foo = tcCoarsest rsubr' tr' x y xy
      bar = tcCoarsest rsubr' tr' y z yz
  in tr' _ _ _ foo bar

tcIncreasing : {a : Type} -> Increasing (TC {a})
tcIncreasing rel1 rel2 f x z (TCIncl xz) = TCIncl (f x z xz)
tcIncreasing rel1 rel2 f x z (TCTrans {y} xy yz) =
  let bar = tcIncreasing rel1 rel2 f x y xy
      baz = tcIncreasing rel1 rel2 f y z yz
  in tcTransitive _ _ _ bar baz

tcInflationary : {a : Type} -> Inflationary (TC {a})
tcInflationary rel x y = TCIncl

tcIdempotent : {a : Type} -> Idempotent (TC {a})
tcIdempotent {a} rel = MkEquivalent this that
  where
    this : (x : a) -> (y : a) -> TC rel x y -> TC (TC rel) x y
    this x y xy = TCIncl xy

    that : (x : a) -> (z : a) -> TC (TC rel) x z -> TC rel x z
    that x z (TCIncl xz) = xz
    that x z (TCTrans {y} xy yz) =
      let bob = that x y xy
          sarah = that y z yz
      in tcTransitive _ _ _ bob sarah

||| Transitive closure is a closure operator.
tcIsClosureOperator : ClosureOperator TC
tcIsClosureOperator = MkClosureOperator tcInflationary tcIncreasing tcIdempotent

-- This actually follows immediately from the fact that the transitive
-- closure is inflationary, but it's easy enough to prove directly.
||| The transitive closure of a reflexive relation is reflexive.
tcReflRefl : {rel : Rel a} -> Reflexive eq rel -> Reflexive eq (TC rel)
tcReflRefl rfl x y xEQy = TCIncl (rfl x y xEQy)

||| Alternative definition of transitive closure
data TC' : Rel a -> Rel a where
  TCIncl' : rel x y -> TC' rel x y
  TCTrans' : rel x y -> TC' rel y z -> TC' rel x z

tcTransitive' : {rel : Rel a} -> Transitive (TC' rel)
tcTransitive' x y z (TCIncl' xy) yz = TCTrans' xy yz
tcTransitive' x y z (TCTrans' {y=y'} xy' y'y) yz = 
    TCTrans' xy' (tcTransitive' y' y z y'y yz)

tcThenTC' : {rel : Rel a} -> TC rel `Coarser` TC' rel
tcThenTC' {a} {rel} = tcCoarsest {rel} {rel'=TC' rel} (\x,y,xy=>TCIncl' xy) (tcTransitive' {rel})

tc'ThenTC : {rel : Rel a} -> TC' rel `Coarser` TC rel
tc'ThenTC x z (TCIncl' xz) = TCIncl xz
tc'ThenTC x z (TCTrans' {y} xy yz) = TCTrans (TCIncl xy) (tc'ThenTC y z yz)

||| The two definitions of transitive closure are equivalent.
tcEquivTC' : {rel : Rel a} -> Equivalent (TC rel) (TC' rel)
tcEquivTC' = MkEquivalent tcThenTC' tc'ThenTC
