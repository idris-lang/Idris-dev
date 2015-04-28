||| General definitions and theorems about relations
module Relations.Basics

%default total
%access public

||| A binary relation on a type
|||
||| @ a an arbitrary type
Rel : (a : Type) -> Type
Rel a = a -> a -> Type

||| Express that a relation is coarser than another
Coarser : {a : Type} -> (R1, R2 : Rel a) -> Type
Coarser {a} R1 R2 = (x,y : a) -> R1 x y -> R2 x y

||| The intersection of two relations
Intersection : {a : Type} -> (rel1, rel2 : Rel a) -> Rel a
Intersection rel1 rel2 x y = (rel1 x y, rel2 x y)

||| The union of two relations
Union : {a : Type} -> (rel1, rel2 : Rel a) -> Rel a
Union rel1 rel2 x y = Either (rel1 x y) (rel2 x y)

||| Express that a relation is equivalent to another
data Equivalent : {a : Type} -> (R1, R2 : Rel a) -> Type where
  MkEquivalent : {R1,R2 : Rel a} -> Coarser R1 R2 -> Coarser R2 R1 -> Equivalent R1 R2

infix 5 ~=
(~=) : {a : Type} -> (R1, R2 : Rel a) -> Type
rel1 ~= rel2 = rel1 `Equivalent` rel2

Inflationary : (Rel a -> Rel a) -> Type
Inflationary {a} f = (rel : Rel a) -> rel `Coarser` f rel

Increasing : (Rel a -> Rel a) -> Type
Increasing {a} f = (rel1, rel2 : Rel a) -> rel1 `Coarser` rel2 -> f rel1 `Coarser` f rel2

Idempotent : (Rel a -> Rel a) -> Type
Idempotent {a} f = (rel : Rel a) -> f rel ~= f (f rel)

data ClosureOperator : (Rel a -> Rel a) -> Type where
  MkClosureOperator : (infl : Inflationary f) ->
                      (incr : Increasing f) ->
                      (idem : Idempotent f) ->
                      ClosureOperator f

||| Take the inverse image of a relation under a function.
||| ``r `On` f`` is the inverse image of `r` under `f`.
On : (r : Rel b) -> (f : a -> b) -> Rel a
On {a} rb f x y = rb (f x) (f y)

||| An approximate fixed point of a function between relations.
Fixed : (f : Rel a -> Rel a) -> Rel a -> Type
Fixed {a} f rel = rel ~= f rel

{-
TODO Finish this, if it's true, and if possible factor out into smaller
useful lemmas.
intersectionClosedClosed : (f : Rel a -> Rel a) ->
                           (ClosureOperator f) ->
                           {rel1, rel2 : Rel a} ->
                           Fixed f rel1 -> Fixed f rel2 ->
                           Fixed f (rel1 `Intersection` rel2)
intersectionClosedClosed {a} {rel1} {rel2} f (MkClosureOperator infl incr idem) fixed1 fixed2 =
  MkEquivalent this that
  where
    this : (x : a) ->
           (y : a) ->
           Intersection rel1 rel2 x y -> f (Intersection rel1 rel2) x y
    that : (x : a) ->
           (y : a) ->
           f (Intersection rel1 rel2) x y -> Intersection rel1 rel2 x y
    that x y fixy = (?that1, ?that2)
-}

||| Proof that a relation is transitive
Transitive : Rel a -> Type
Transitive {a} rel = (x,y,z:a) -> x `rel` y -> y `rel` z -> x `rel` z

||| Proof that a relation is antitransitive
Antitransitive : Rel a -> Type
Antitransitive {a} rel = (x,y,z:a) -> x `rel` y -> y `rel` z -> x `rel` z -> Void

||| Proof that a relation is symmetric
Symmetric : Rel a -> Type
Symmetric {a} rel = (x,y:a) -> x `rel` y -> y `rel` x

||| Proof that a relation is antisymmetric
Antisymmetric : Rel a -> Type
Antisymmetric {a} rel = (x,y : a) -> x `rel` y -> y `rel` x -> x = y

||| Proof that a relation is asymmetric
Asymmetric : Rel a -> Type
Asymmetric {a} rel = (x,y : a) -> x `rel` y -> y `rel` x -> Void

||| Proof that a relation is reflexive
Reflexive : Rel a -> Type
Reflexive {a} rel = (x:a) -> x `rel` x

||| Proof that a relation is irreflexive
Irreflexive : Rel a -> Type
Irreflexive {a} rel = (x:a) -> x `rel` x -> Void

||| Proof that a relation is total
Total : Rel a -> Type
Total {a} rel = (x,y:a) -> Either (x `rel` y) (y `rel` x)

||| Proof that a relation is connected
Connected : Rel a -> Type
Connected {a} rel = (x,y:a) -> Not (x `rel` y) -> Not (y `rel` x) -> x = y

||| Proof that a relation is a comparison
Comparison : Rel a -> Type
Comparison {a} rel = (x,y,z:a) -> x `rel` z -> Either (x `rel` y) (y `rel` z)



asymmetricIsAntisymmetric : Asymmetric rel -> Antisymmetric rel
asymmetricIsAntisymmetric asym x y xy yx = absurd $ asym x y xy yx

totalIsConnected : {rel : Rel a} -> Total rel -> Connected rel
totalIsConnected tot x y xy yx with (tot x y)
  totalIsConnected tot x y xnoty ynotx | (Left q) = absurd $ xnoty q
  totalIsConnected tot x y xnoty ynotx | (Right r) = absurd $ ynotx r

asymmetricIsIrreflexive : Asymmetric rel -> Irreflexive rel
asymmetricIsIrreflexive asym x xRx = asym x x xRx xRx

asymmetricComparisonIsTransitive : {rel : Rel a} -> Asymmetric rel -> Comparison rel -> Transitive rel
asymmetricComparisonIsTransitive asym cmpr x y z xy yz with (cmpr _ z _ xy)
  asymmetricComparisonIsTransitive asym cmpr x y z xy yz | (Left xz) = xz
  asymmetricComparisonIsTransitive asym cmpr x y z xy yz | (Right zy) = absurd (asym _ _ yz zy)

irreflexiveTransitiveIsAsymmetric : {rel : Rel a} -> Irreflexive rel -> Transitive rel -> Asymmetric rel
irreflexiveTransitiveIsAsymmetric {rel} irref trns x y xy yx =
  irref x (trns x y x xy yx)

totalIsReflexive : Total rel -> Reflexive rel
totalIsReflexive {rel} tot x = either id id (tot x x)

cmptrns : Antisymmetric rel ->
          Total rel ->
          Comparison rel ->
          Transitive rel
cmptrns antsym tot cmpr x y z xy yz with (tot x z)
  cmptrns antsym tot cmpr x y z xy yz | (Left xz) = xz
  cmptrns antsym tot cmpr x y z xy yz | (Right zx) with (cmpr z y x zx)
    cmptrns antsym tot cmpr x y z xy yz | (Right zx) | (Left zy) =
      let yEQz = antsym _ _ yz zy
      in replace yEQz xy
    cmptrns antsym tot cmpr x y z xy yz | (Right zx) | (Right yx) =
      let yEQx = antsym _ _ yx xy
      in ?cmptrns_rhs_3

transitiveTotalIsComparison : Transitive rel ->
                              Total rel ->
                              Comparison rel
transitiveTotalIsComparison trns tot x y z yz with (tot x y)
  transitiveTotalIsComparison trns tot x y z yz | (Left xy) = Left xy
  transitiveTotalIsComparison trns tot x y z yz | (Right yx) = Right (trns y x z yx yz)

---------- Proofs ----------

-- TODO Figure out how to get rid of this.

Relations.Basics.cmptrns_rhs_3 = proof
  intros
  rewrite yEQx 
  exact yz

