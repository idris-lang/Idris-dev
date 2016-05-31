%default total

binary_relation : (a : Type) -> Type
binary_relation a = (x, y : a) -> Type

reflexive : (a : Type) -> (r : binary_relation a) -> Type
reflexive a r = (x : a) -> r x x

symmetric : (a : Type) -> (r : binary_relation a) -> Type
symmetric a r = (x, y : a) -> r x y -> r y x

data Equal : (a : Type) -> binary_relation a where
  Same : (a : Type) -> (x : a) -> Equal a x x

Equal_reflexive : (a : Type) -> reflexive a (Equal a)
Equal_reflexive a x = Same a x

Equal_symmetric : (a : Type) -> symmetric a (Equal a)
-- Equal_symmetric : (a : Type) -> (x, y : a) -> Equal a x y -> Equal a y x
Equal_symmetric a x x (Same a x) = Same a x

