module Data.Always

import Data.Elem

%default total

data Always : (x -> Type) -> List x -> Type where
  Nil : Always f []
  (::) : f ty -> Always f l -> Always f (ty :: l)

index : Elem x xs -> Always f xs -> f x
index Here (x :: _) = x
index (There elem) (_ :: xs) = index elem xs

replaceAt : Elem x xs -> f x -> Always f xs -> Always f xs
replaceAt Here element (_ :: xs) = element :: xs
replaceAt (There n) element (x :: xs) = x :: replaceAt n element xs

replaceAndIndex : {elements:Always f xs} -> index elem (replaceAt elem x elements) = x
replaceAndIndex {elem = Here} {elements = Nil} impossible
replaceAndIndex {elem = Here} {elements = (_ :: _)} = Refl
replaceAndIndex {elem = There elem} {elements = Nil} impossible
replaceAndIndex {elem = There elem} {elements = (_ :: _)} = replaceAndIndex

replaceAndIndexElsewhere : {elements:Always f xs} -> (elem1 = elem2 -> Void) -> index elem1 (replaceAt elem2 x elements) = index elem1 elements
replaceAndIndexElsewhere f {elem1 = Here} {elem2 = Here} = void (f Refl)
replaceAndIndexElsewhere _ {elem1 = Here} {elements = Nil} impossible
replaceAndIndexElsewhere _ {elem1 = There _} {elements = Nil} impossible
replaceAndIndexElsewhere _ {elem1 = Here} {elem2 = There _} {elements = _ :: _} = Refl
replaceAndIndexElsewhere _ {elem1 = There _} {elem2 = Here} {elements = _ :: _} = Refl
replaceAndIndexElsewhere f {elem1 = There _} {elem2 = There _} {elements = _ :: _} = replaceAndIndexElsewhere (f . cong)

replaceOrder : {elements:Always f xs} -> (elem1 = elem2 -> Void) -> replaceAt elem2 x2 (replaceAt elem1 x1 elements) = replaceAt elem1 x1 (replaceAt elem2 x2 elements)
replaceOrder f {elem1 = Here} {elem2 = Here} = void (f Refl)
replaceOrder _ {elem1 = Here} {elements = Nil} impossible
replaceOrder _ {elem1 = There _} {elements = Nil} impossible
replaceOrder _ {elem1 = Here} {elem2 = There _} {elements = _ :: _} = Refl
replaceOrder _ {elem1 = There _} {elem2 = Here} {elements = _ :: _} = Refl
replaceOrder f {elem1 = There _} {elem2 = There _} {elements = _ :: _} = cong (replaceOrder (f . cong))
