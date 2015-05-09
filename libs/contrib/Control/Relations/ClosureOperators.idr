||| General definitions and theorems about relations
module Control.Relations.ClosureOperators
import Basics

%default total
%access public

||| A closure operator on relations is one that is inflationary,
||| increasing, and idempotent.
data ClosureOperator : (Rel a -> Rel a) -> Type where
  MkClosureOperator : (infl : Inflationary f) ->
                      (incr : Increasing f) ->
                      (idem : Idempotent f) ->
                      ClosureOperator f


intersectionClosedClosed : (f : Rel a -> Rel a) ->
                           (ClosureOperator f) ->
                           {rel1, rel2 : Rel a} ->
                           Fixed f rel1 -> Fixed f rel2 ->
                           Fixed f (rel1 `Intersection` rel2)
intersectionClosedClosed {a} {rel1} {rel2} f (MkClosureOperator infl incr idem) fixed1 fixed2 =
  MkEquivalent ?this ?that
  where
    this : (x,y : a) -> Intersection rel1 rel2 x y -> f (Intersection rel1 rel2) x y
    this x y (xR1y, xR2y) = infl (Intersection rel1 rel2) x y (xR1y, xR2y)

    that : (x,y : a) -> f (Intersection rel1 rel2) x y -> Intersection rel1 rel2 x y
    that x y fr1r2xy = ?that_rhs
