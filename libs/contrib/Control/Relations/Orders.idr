||| General definitions and theorems about preorders, orders, etc.
module Relations.Orders
import Basics

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
data LinearOrder : (eq : Rel a) -> Rel a -> Type where
  MkLinearOrder :  (eqEquiv : Equivalence eq) ->
                   (irref : Irreflexive eq rel) ->
                   (asym : Asymmetric rel) ->
                   (trns : Transitive rel) ->
                   (cmpr : Comparison rel) ->
                   (conn : Connected eq rel) ->
                   LinearOrder eq rel

||| A strict total order as defined in the Agda standard library. Unlike a
||| a linear order, a strict total order is guaranteed to be decidable. Unlike
||| the reflexive reduction of a total order, a strict total order is
||| guaranteed to be transitive.
data StrictTotalOrder : (eq : Rel a) -> Rel a -> Type where
  MkStrictTotalOrder :
      {default equalityIsEquivalence eqEquiv : Equivalence eq} ->
      (trns : Transitive rel) ->
      (compare : Trichotomous {eq} rel) ->
      (respEq : rel `Respects2` eq) ->
      StrictTotalOrder {eq} rel
      
||| The full complement of basic total order properties as described on nLab.
||| To construct these, use `mkTotalOrderTrns` or `mkTotalOrderCmpr`.
data TotalOrder : (eq : Rel a) -> Rel a -> Type where
  MkTotalOrder :  (ord : Order eq rel) ->
                  (tot : Total rel) ->
                  (cmpr : Comparison rel) ->
                  TotalOrder eq rel

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

mkLinearOrderTrans : (eqEquiv : Equivalence eq) ->
                     (irref : Irreflexive eq rel) ->
                     (trns : Transitive rel) ->
                     (cmpr : Comparison rel) ->
                     (conn : Connected eq rel) ->
                     LinearOrder eq rel

mkLinearOrderTrans eqEquiv irref trns cmpr conn =
  MkLinearOrder eqEquiv irref (irreflexiveTransitiveIsAsymmetric eqEquiv irref trns)
      trns cmpr conn



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
