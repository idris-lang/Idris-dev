||| General definitions and theorems about preorders, orders, etc.
module Relations.Orders
import Basics

%default total
%access public

||| A preorder is a reflexive and transitive relation.
data Preorder : Rel a -> Type where
  MkPreorder : (rfl : Reflexive rel) -> (trns : Transitive rel) -> Preorder rel

||| And order is a reflexive, transitive, and symmetric relation.
||| Note that antisymmetry is categorically "evil", since it forces
||| actual equality.
data Order : Rel a -> Type where
  MkOrder : Reflexive rel -> Transitive rel -> Antisymmetric rel -> Order rel

||| The full complement of basic characteristics of linear orders
||| according to nLab. To construct this, use either `mkLinearOrderAsym`
||| or `mkLinearOrderTrans`.
data LinearOrder : Rel a -> Type where
  MkLinearOrder : (irref : Irreflexive rel) ->
                   (asym : Asymmetric rel) ->
                   (trns : Transitive rel) ->
                   (cmpr : Comparison rel) ->
                   (conn : Connected rel) ->
                   LinearOrder rel

||| The full complement of basic total order properties as described on nLab.
||| To construct these, use `mkTotalOrderTrns` or `mkTotalOrderCmpr`.
data TotalOrder : Rel a -> Type where
  MkTotalOrder : (rfl : Reflexive rel) ->
                  (trns : Transitive rel) ->
                  (antsym : Antisymmetric rel) ->
                  (tot : Total rel) ->
                  (cmpr : Comparison rel) ->
                  TotalOrder rel


orderIsPreorder : Order rel -> Preorder rel
orderIsPreorder (MkOrder f g _) = MkPreorder f g

mkLinearOrderAsym : {rel : Rel a} ->
                 (asym : Asymmetric rel) ->
                 (cmpr : Comparison rel) ->
                 (conn : Connected rel) ->
                 LinearOrder rel
mkLinearOrderAsym {a} {rel} asym cmpr conn =
  MkLinearOrder (asymmetricIsIrreflexive asym)
                 asym
                 (asymmetricComparisonIsTransitive asym cmpr)
                 cmpr
                 conn

mkLinearOrderTrans : {rel : Rel a} ->
                     (irref : Irreflexive rel) ->
                     (trns : Transitive rel) ->
                     (cmpr : Comparison rel) ->
                     (conn : Connected rel) ->
                     LinearOrder rel
mkLinearOrderTrans irref trns cmpr conn =
  MkLinearOrder irref (irreflexiveTransitiveIsAsymmetric irref trns) trns cmpr conn


mkTotalOrderCmpr : (antsym : Antisymmetric rel) ->
                   (tot : Total rel) ->
                   (cmpr : Comparison rel) ->
                   TotalOrder rel
mkTotalOrderCmpr antsym tot cmpr =
  MkTotalOrder (totalIsReflexive tot) (cmptrns antsym tot cmpr) antsym tot cmpr

mkTotalOrderTrns : (trns : Transitive rel) ->
                   (antsym : Antisymmetric rel) ->
                   (tot : Total rel) ->
                   TotalOrder rel
mkTotalOrderTrns trns antsym tot =
  MkTotalOrder  (totalIsReflexive tot) trns antsym tot (transitiveTotalIsComparison trns tot)
