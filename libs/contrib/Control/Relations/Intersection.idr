module Control.Relations.Set
import Basics

%default total
%access public

||| A family of relations on a type
Family : Type -> Type -> Type
Family a ix = (i : ix) -> Rel a

IntersectionMany : Family a ix -> Rel a
IntersectionMany {ix} f x y = (i : ix) -> f i x y

UnionMany : Family a ix -> Rel a
UnionMany {ix} f x y = (i ** f i x y)
