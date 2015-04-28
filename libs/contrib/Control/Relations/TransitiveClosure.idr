||| General definitions and theorems about relations
module Relations.TransitiveClosure
import Basics
import Equivalence
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
tcSmallest : {rel, rel' : Rel a} -> rel `Coarser` rel' -> Transitive rel' ->
             TC rel `Coarser` rel'
tcSmallest rsubr' tr' x y (TCIncl xy) = rsubr' _ _ xy
tcSmallest rsubr' tr' x z (TCTrans {y} xy yz) =
  let foo = tcSmallest rsubr' tr' x y xy
      bar = tcSmallest rsubr' tr' y z yz
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

tcReflRefl : {rel : Rel a} -> Reflexive rel -> Reflexive (TC rel)
tcReflRefl {rel} f x = TCIncl (f x)

||| Alternative definition of transitive closure
data TC' : Rel a -> Rel a where
  TCIncl' : rel x y -> TC' rel x y
  TCTrans' : rel x y -> TC' rel y z -> TC' rel x z

tcTransitive' : {rel : Rel a} -> Transitive (TC' rel)
tcTransitive' x y z (TCIncl' xy) yz = TCTrans' xy yz
tcTransitive' x y z (TCTrans' {y=y'} xy' y'y) yz = 
    TCTrans' xy' (tcTransitive' y' y z y'y yz)

tcThenTC' : {rel : Rel a} -> TC rel `Coarser` TC' rel
tcThenTC' {a} {rel} = tcSmallest {rel} {rel'=TC' rel} (\x,y,xy=>TCIncl' xy) (tcTransitive' {rel})

tc'ThenTC : {rel : Rel a} -> TC' rel `Coarser` TC rel
tc'ThenTC x z (TCIncl' xz) = TCIncl xz
tc'ThenTC x z (TCTrans' {y} xy yz) = TCTrans (TCIncl xy) (tc'ThenTC y z yz)

||| The two definitions of transitive closure are equivalent.
tcEquivTCp : {rel : Rel a} -> Equivalent (TC rel) (TC' rel)
tcEquivTCp {rel} = MkEquivalent tcThenTC' tc'ThenTC
