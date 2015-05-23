||| General definitions and theorems about preorders, orders, linear orders,
||| strict total orders, and total orders.
module Control.Relations.Orders
import Control.Relations.Basics
import Control.Relations.ReflexiveClosure

%default total
%access public

||| A preorder is a reflexive and transitive relation. Here, reflexivity
||| is relative to some equivalence relation.
data Preorder : (eq : Rel a) -> Rel a -> Type where
  MkPreorder : (eqEquiv : Equivalence eq) ->
               (rfl : Reflexive eq rel) -> (trns : Transitive rel) -> Preorder eq rel

||| And order is a reflexive, transitive, and symmetric relation.
||| Note that antisymmetry is categorically "evil", since it forces
||| actual equality.
data Order : (eq : Rel a) -> Rel a -> Type where
  MkOrder : Preorder eq rel -> Antisymmetric eq rel -> Order eq rel

||| The full complement of basic characteristics of linear orders
||| according to nLab. To construct this, use either `mkLinearOrderAsym`
||| or `mkLinearOrderTrans`.
record LinearOrder (eq : Rel a) (rel : Rel a) where
  constructor MkLinearOrder
  eqEquiv : Equivalence eq
  irref : Irreflexive eq rel
  asym : Asymmetric rel
  trns : Transitive rel
  cmpr : Comparison rel
  conn : Connected eq rel

||| A strict total order as defined in the Agda standard library. Unlike a
||| a linear order, a strict total order is guaranteed to be decidable. Unlike
||| the reflexive reduction of a total order, a strict total order is
||| guaranteed to be transitive. A strict total order is guaranteed to be a linear order.
record StrictTotalOrder (eq : Rel a) (rel : Rel a) where
  constructor MkStrictTotalOrder
  eqEquiv : Equivalence eq
  respEq : rel `Respects2` eq
  trns : Transitive rel
  cmpr : Trichotomous eq rel

||| The full complement of basic total order properties as described on nLab.
||| To construct these, use `mkTotalOrderTrns` or `mkTotalOrderCmpr`.
record TotalOrder (eq : Rel a) (rel : Rel a) where
  constructor MkTotalOrder
  ord : Order eq rel
  tot : Total rel
  cmpr : Comparison rel

||| An asymmetric, connected comparison is a linear order.
mkLinearOrderAsym :
                 (eqEquiv : Equivalence eq) ->
                 (relRespEq : rel `Respects2` eq) ->
                 (asym : Asymmetric rel) ->
                 (cmpr : Comparison rel) ->
                 (conn : Connected eq rel) ->
                 LinearOrder eq rel
mkLinearOrderAsym {eq} {rel} eqEquiv relRespEq asym cmpr conn =
  MkLinearOrder eqEquiv
      (asymmetricIsIrreflexive eqEquiv relRespEq asym)
      asym
      (asymmetricComparisonIsTransitive asym cmpr)
      cmpr
      conn

mkLinearOrderAsymSimple :
                 (asym : Asymmetric rel) ->
                 (cmpr : Comparison rel) ->
                 (conn : Connected (~=~) rel) ->
                 LinearOrder (~=~) rel
mkLinearOrderAsymSimple asym cmpr conn =
  mkLinearOrderAsym equalityIsEquivalence allRespectEquality2 asym cmpr conn

||| An irreflexive, transitive, connected comparison is a linear order.
mkLinearOrderTrans : (eqEquiv : Equivalence eq) ->
                     (irref : Irreflexive eq rel) ->
                     (trns : Transitive rel) ->
                     (cmpr : Comparison rel) ->
                     (conn : Connected eq rel) ->
                     LinearOrder eq rel

mkLinearOrderTrans eqEquiv irref trns cmpr conn =
  MkLinearOrder eqEquiv irref (irreflexiveTransitiveIsAsymmetric eqEquiv irref trns)
      trns cmpr conn

stoAsymmetric : StrictTotalOrder eq rel -> Asymmetric rel
stoAsymmetric foo x y xRy yRx with (cmpr foo x y)
  | (TriLT z f g) = g yRx
  | (TriEQ f z g) = g yRx
  | (TriGT f g z) = f xRy

stoComparison : StrictTotalOrder eq rel -> Comparison rel
stoComparison sto x y z xRz with (cmpr sto x y)
  | (TriLT w f g) = Left w
  | (TriEQ f w g) with (cmpr sto y z)
    stoComparison sto x y z xRz | (TriEQ f w g) | (TriLT s t u) = Right s
    stoComparison sto x y z xRz | (TriEQ f xEQy g) | (TriEQ s yEQz u) =
       let xRy = case respEq sto of (this, _) => this x _ _ (getSymmetric (eqEquiv sto) y z yEQz) xRz in Left xRy
    stoComparison sto x y z xRz | (TriEQ f xEQy g) | (TriGT s t zRy) =
      Left $ trns sto x z y xRz zRy
  | (TriGT f g w) with (cmpr sto y z)
    stoComparison sto x y z xRz | (TriGT f g _) | (TriLT yRz s t) = Right yRz
    stoComparison sto x y z xRz | (TriGT f g _) | (TriEQ w yEQz t) =
      Left $ case respEq sto of (this,_) => this x _ _ (getSymmetric (eqEquiv sto) y z yEQz) xRz
    stoComparison sto x y z xRz | (TriGT f g _) | (TriGT w s zRy) =
                absurd . f $ trns sto _ z _ xRz zRy

stoConnected : StrictTotalOrder eq rel -> Connected eq rel
stoConnected sto x y notxRy notyRx with (cmpr sto x y)
  | (TriLT z f g) = absurd (notxRy z)
  | (TriEQ f z g) = z
  | (TriGT f g z) = absurd (notyRx z)

||| A strict total order is a linear order.
strictTotalOrderIsLinear : StrictTotalOrder eq rel -> LinearOrder eq rel
strictTotalOrderIsLinear sto@(MkStrictTotalOrder eqEquiv respEq trns compare) =
  mkLinearOrderAsym eqEquiv respEq (stoAsymmetric sto) (stoComparison sto) (stoConnected sto)

||| An antisymmetric, total comparison is a total order.
mkTotalOrderCmpr : {rel : Rel a} -> (eqEquiv : Equivalence eq) ->
                   (relRespEq : rel `Respects2` eq) ->
                   (antsym : Antisymmetric eq rel) ->
                   (tot : Total rel) ->
                   (cmpr : Comparison rel) ->
                   TotalOrder eq rel
mkTotalOrderCmpr {eq} {rel} eqEquiv relRespEq antsym tot cmpr =
  MkTotalOrder (MkOrder {eq} pre antsym)  tot cmpr
   where
     trns : Transitive rel
     trns = cmptrns relRespEq antsym tot cmpr
     rfl : Reflexive eq rel --  (x,y : a) -> eq x y -> rel x y
     rfl = totalIsReflexive eqEquiv relRespEq tot
     pre : Preorder eq rel
     pre = MkPreorder {eq} eqEquiv rfl trns

mkTotalOrderCmprSimple :
                   (antsym : Antisymmetric (~=~) rel) ->
                   (tot : Total rel) ->
                   (cmpr : Comparison rel) ->
                   TotalOrder (~=~) rel
mkTotalOrderCmprSimple =
  mkTotalOrderCmpr equalityIsEquivalence allRespectEquality2

||| A transitive, antisymmetric, total relation is a total order.
mkTotalOrderTrns : {rel : Rel a} ->
                   (eqEquiv : Equivalence eq) ->
                   (relRespEq : rel `Respects2` eq) ->
                   (trns : Transitive rel) ->
                   (antsym : Antisymmetric eq rel) ->
                   (tot : Total rel) ->
                   TotalOrder eq rel

mkTotalOrderTrns {a} {eq} {rel} eqEquiv relRespEq trns antsym tot =
  MkTotalOrder (MkOrder {eq} pre antsym) tot cmpr
  where
    rfl : Reflexive eq rel
    rfl = totalIsReflexive eqEquiv relRespEq tot
    pre : Preorder eq rel
    pre = MkPreorder eqEquiv rfl trns
    cmpr : Comparison rel
    cmpr = transitiveTotalIsComparison trns tot
