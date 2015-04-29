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

||| Proof that a relation is transitive
Transitive : Rel a -> Type
Transitive {a} rel = (x,y,z:a) -> x `rel` y -> y `rel` z -> x `rel` z

||| Proof that a relation is antitransitive
Antitransitive : Rel a -> Type
Antitransitive {a} rel = (x,y,z:a) -> x `rel` y -> y `rel` z -> x `rel` z -> Void

||| Proof that a relation is symmetric
Symmetric : Rel a -> Type
Symmetric {a} rel = (x,y:a) -> x `rel` y -> y `rel` x

||| Proof that a relation is antisymmetric. Takes as an argument
||| the desired equivalence.
Antisymmetric : (eq : Rel a) -> Rel a -> Type
Antisymmetric {a} eq rel = (x,y : a) -> x `rel` y -> y `rel` x -> x `eq` y

||| Proof that a relation is asymmetric
Asymmetric : Rel a -> Type
Asymmetric {a} rel = (x,y : a) -> x `rel` y -> y `rel` x -> Void

||| Proof that a relation is reflexive relative to `(~=~)`
Reflexive' : Rel a -> Type
Reflexive' {a} rel = (x:a) -> x `rel` x

||| Proof that a relation is irreflexive relative to `(~=~)`
Irreflexive' : Rel a -> Type
Irreflexive' {a} rel = (x:a) -> x `rel` x -> Void

||| Proof that a relation is reflexive
Reflexive : (eq : Rel a) -> Rel a -> Type
Reflexive {a} eq rel = (x,y : a) -> x `eq` y -> x `rel` y

||| Proof that a relation is irreflexive
Irreflexive : (eq : Rel a) -> Rel a -> Type
Irreflexive {a} eq rel = (x,y:a) -> x `eq` y -> x `rel` y -> Void


||| An equivalence relation is a reflexive, transitive, and symmetric
||| relation.
data Equivalence : Rel a -> Type where
  MkEquivalence : (rfl : Reflexive' rel) -> (trns : Transitive rel) ->
                  (symm : Symmetric rel) -> Equivalence rel

getReflexive' : Equivalence rel -> Reflexive' rel
getReflexive' (MkEquivalence rfl trns symm) = rfl

getSymmetric : Equivalence rel -> Symmetric rel
getSymmetric (MkEquivalence rfl trns symm) = symm

getTransitive : Equivalence rel -> Transitive rel
getTransitive (MkEquivalence rfl trns symm) = trns

||| The intersection of two relations
Intersection : {a : Type} -> (rel1, rel2 : Rel a) -> Rel a
Intersection rel1 rel2 x y = (rel1 x y, rel2 x y)

||| The union of two relations
Union : {a : Type} -> (rel1, rel2 : Rel a) -> Rel a
Union rel1 rel2 x y = Either (rel1 x y) (rel2 x y)

||| Express that a relation is equivalent to another
data Equivalent : {a : Type} -> (R1, R2 : Rel a) -> Type where
  MkEquivalent : {R1,R2 : Rel a} -> Coarser R1 R2 -> Coarser R2 R1 -> Equivalent R1 R2

||| An operation on relations is inflationary if the result is always
||| finer than the argument.
Inflationary : (Rel a -> Rel a) -> Type
Inflationary {a} f = (rel : Rel a) -> rel `Coarser` f rel

||| An operation on relations is deflationary if the result is always
||| coarser than the argument
Deflationary : (Rel a -> Rel a) -> Type
Deflationary {a} f = (rel : Rel a) -> f rel `Coarser` rel

||| An operation on relations is increasing if the result of a coarser
||| argument is always coarser.
Increasing : (Rel a -> Rel a) -> Type
Increasing {a} f = (rel1, rel2 : Rel a) -> rel1 `Coarser` rel2 -> f rel1 `Coarser` f rel2

||| An operation on relations is decreasing if the result of a finer
||| argument is always coarser.
Decreasing : (Rel a -> Rel a) -> Type
Decreasing {a} f = (rel1, rel2 : Rel a) -> rel1 `Coarser` rel2 -> f rel2 `Coarser` f rel1

||| An operation on relations is (approximately) idempotent if the
||| result of applying it twice is always equivalent to the result of applying
||| it once.
Idempotent : {default Equivalent eq : Rel (Rel a)} -> (Rel a -> Rel a) -> Type
Idempotent {eq} {a} f = (rel : Rel a) -> f rel `eq` f (f rel)

||| A closure operator on relations is one that is inflationary,
||| increasing, and idempotent.
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
Fixed {a} f rel = rel `Equivalent` f rel

||| Proof that a relation is total
Total : Rel a -> Type
Total {a} rel = (x,y:a) -> Either (x `rel` y) (y `rel` x)

||| Proof that a relation is connected
Connected : (eq : Rel a) -> Rel a -> Type
Connected {a} eq rel = (x,y:a) -> Not (x `rel` y) -> Not (y `rel` x) -> x `eq` y

||| Proof that a relation is a comparison
Comparison : Rel a -> Type
Comparison {a} rel = (x,y,z:a) -> x `rel` z -> Either (x `rel` y) (y `rel` z)

||| Proof that a relation is decidable
Decidable : Rel a -> Type
Decidable {a} rel = (x,y:a) -> Dec (rel x y)

Respects : (a -> Type) -> Rel a -> Type
Respects {a} p rel = (x,y : a) -> rel x y -> p x -> p y

Respects2 : Rel a -> Rel a -> Type
Respects2 {a} rel sim = ((p : a) -> rel p `Respects` sim, (q : a) -> flip rel q `Respects` sim)

data Tri : Type -> Type -> Type -> Type where
  TriLT : (x : a) -> (y : Not b) -> (z : Not c) -> Tri a b c
  TriEQ : (x : Not a) -> (y : b) -> (z : Not c) -> Tri a b c
  TriGT : (x : Not a) -> (y : Not b) -> (z : c) -> Tri a b c

Trichotomous : (eq : Rel a) -> (rel : Rel a) -> Type
Trichotomous {a} eq rel = (x,y : a) -> Tri (rel x y) (eq x y) (rel y x)

equalityIsReflexive' : Reflexive' (~=~)
equalityIsReflexive' x = Refl

equalityIsSymmetric : Symmetric (~=~)
equalityIsSymmetric x y = sym

equalityIsTransitive : Transitive (~=~)
equalityIsTransitive x y z = trans

||| The `(~=~)` relation on any given type is an equivalence.
equalityIsEquivalence : Equivalence (~=~)
equalityIsEquivalence = MkEquivalence (\x => Refl) (\x,y,z => trans) (\x,y=>sym)

||| Equivalence of relations is an equivalence relation.
equivalentIsEquivalence : Equivalence Equivalent 
equivalentIsEquivalence = MkEquivalence rfl trns symm
  where 
    rfl : (rel : a -> a -> Type) -> Equivalent rel rel
    rfl rel = MkEquivalent (\x,y,rel=>rel) (\x,y,rel=>rel)
    symm : (rel1 : a -> a -> Type) -> 
           (rel2 : a -> a -> Type) -> Equivalent rel1 rel2 -> Equivalent rel2 rel1
    symm rel1 rel2 (MkEquivalent f g) = MkEquivalent g f
    trns : (rel1 : a -> a -> Type) ->
           (rel2 : a -> a -> Type) ->
           (rel3 : a -> a -> Type) ->
           Equivalent rel1 rel2 -> Equivalent rel2 rel3 -> Equivalent rel1 rel3
    trns rel1 rel2 rel3 (MkEquivalent f g) (MkEquivalent h i) =
      MkEquivalent (\x,y,r => h x y (f x y r))
                   (\x,y,r => g x y (i x y r))


equalityIsAntisymmetric : (Equivalence eq) ->
                          Antisymmetric eq (~=~)
equalityIsAntisymmetric eqEquiv x y xy yx = rewrite xy in getReflexive' eqEquiv y

allRespectEquality2 : rel `Respects2` (~=~)
allRespectEquality2 = ((\_,p,q,eq,xrp => rewrite sym eq in xrp) ,
                          (\_,p,q,eq,xrp => rewrite sym eq in xrp))

asymmetricIsAntisymmetric : Asymmetric rel -> Antisymmetric eq rel
asymmetricIsAntisymmetric asym x y xy yx = absurd $ asym x y xy yx

totalIsConnected : Total rel -> Connected eq rel
totalIsConnected tot x y xy yx with (tot x y)
  totalIsConnected tot x y xnoty ynotx | (Left q) = absurd $ xnoty q
  totalIsConnected tot x y xnoty ynotx | (Right r) = absurd $ ynotx r

||| An asymmetric relation is irreflexive.
asymmetricIsIrreflexive : (eqEquiv : Equivalence eq) ->
                          (relRespEq : rel `Respects2` eq) ->
                          Asymmetric rel -> Irreflexive eq rel
asymmetricIsIrreflexive eqEquiv (relRespEq,_) asym x y xEQy xRELy =
  let xRELx = relRespEq _ _ _ (getSymmetric eqEquiv x y xEQy) xRELy
  in absurd $ asym x x xRELx xRELx

-- Why can't it solve for `rel` on its own?
||| A specialization of `asymmetricIsIrreflexive` to equality.
asymmetricIsIrreflexiveSimple : Asymmetric rel -> Irreflexive (~=~) rel
asymmetricIsIrreflexiveSimple {rel} = asymmetricIsIrreflexive {rel} equalityIsEquivalence allRespectEquality2

||| An asymmetric comparison is transitive
asymmetricComparisonIsTransitive : Asymmetric rel -> Comparison rel -> Transitive rel
asymmetricComparisonIsTransitive asym cmpr x y z xy yz with (cmpr _ z _ xy)
  asymmetricComparisonIsTransitive asym cmpr x y z xy yz | (Left xz) = xz
  asymmetricComparisonIsTransitive asym cmpr x y z xy yz | (Right zy) = absurd (asym _ _ yz zy)

||| An irreflexive, transitive relation is asymmetric.
irreflexiveTransitiveIsAsymmetric : (eqEquiv : Equivalence eq) ->
                                    Irreflexive eq rel ->
                                    Transitive rel -> Asymmetric rel
irreflexiveTransitiveIsAsymmetric eqEquiv irref trns x y xy yx =
  let xx = trns x y x xy yx
  in irref x x (getReflexive' eqEquiv x) xx

||| A specialization of `irreflexiveTransitiveIsAsymmetric` to equality.
irreflexiveTransitiveIsAsymmetricSimple : Irreflexive (~=~) rel -> Transitive rel -> Asymmetric rel
irreflexiveTransitiveIsAsymmetricSimple irr trns = irreflexiveTransitiveIsAsymmetric (equalityIsEquivalence) irr trns

totalIsReflexive' : Total rel -> Reflexive' rel
totalIsReflexive' tot x = either id id (tot x x)

totalIsReflexive : Equivalence eq -> rel `Respects2` eq -> Total rel -> Reflexive eq rel
totalIsReflexive {eq} {rel} eqEquiv resp tot x y xEQy with (tot x y)
  totalIsReflexive {eq} {rel} eqEquiv resp tot x y xEQy | (Left xRELy) = xRELy
  totalIsReflexive {eq} {rel} eqEquiv (f,g) tot x y xEQy | (Right yRELx) = f _ _ _ xEQy xRELx
    where
      yEQx : y `eq` x
      yEQx = getSymmetric eqEquiv x y xEQy

      xRELx : x `rel` x
      xRELx = g x y x yEQx yRELx

-- TODO Rename this.
||| An antisymmetric, total comparison is transitive.
cmptrns : (relRespEq : rel `Respects2` eq) ->
          Antisymmetric eq rel ->
          Total rel ->
          Comparison rel ->
          Transitive rel
cmptrns relRespEq antsym tot cmpr x y z xy yz with (tot x z)
  cmptrns relRespEq antsym tot cmpr x y z xy yz | (Left xz) = xz
  cmptrns relRespEq antsym tot cmpr x y z xy yz | (Right zx) with (cmpr z y x zx)
    cmptrns (f,_) antsym tot cmpr x y z xy yz | (Right zx) | (Left zy) =
      let yEQz = antsym _ _ yz zy
      in f _ y z yEQz xy
    cmptrns (_,g) antsym tot cmpr x y z xy yz | (Right zx) | (Right yx) =
      let yEQx = antsym _ _ yx xy
      in g _ y x yEQx yz

||| A specialization of `cmptrns` to equality.
cmptrnsSimple : Antisymmetric (~=~) rel ->
                Total rel ->
                Comparison rel ->
                Transitive rel
cmptrnsSimple asym tot cmpr = cmptrns allRespectEquality2 asym tot cmpr

||| A transitive total relation is a comparison.
transitiveTotalIsComparison : Transitive rel ->
                              Total rel ->
                              Comparison rel
transitiveTotalIsComparison trns tot x y z yz with (tot x y)
  transitiveTotalIsComparison trns tot x y z yz | (Left xy) = Left xy
  transitiveTotalIsComparison trns tot x y z yz | (Right yx) = Right (trns y x z yx yz)

{-
-- TODO Finish this, if it's true, and if possible factor out into smaller
-- useful lemmas.

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
