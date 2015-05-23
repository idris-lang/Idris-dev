||| General definitions and theorems about relations
module Control.Relations.ClosureOperators
import Control.Relations.Basics

%default total
%access public

||| A closure operator on relations is one that is inflationary,
||| increasing, and idempotent.
data ClosureOperator : (Rel a -> Rel a) -> Type where
  MkClosureOperator : (infl : Inflationary f) ->
                      (incr : Increasing f) ->
                      (idem : Idempotent f) ->
                      ClosureOperator f


-- TODO This admits some generalization, but it's a bit unclear how to
-- generalize it while keeping its purpose easy to understand. The most
-- obvious thing is that the operator only needs to be inflationary and
-- increasing, and need not be idempotent. The other obvious bit is that the two
-- sides of the equivalence proof can be split, yielding lemmas with weaker
-- conditions.

||| The intersection of a family of sets, each of which is closed under
||| a closure operator, is itself closed.
intersectionFamilyClosedClosed : (f : Rel a -> Rel a) ->
                           ClosureOperator f ->
                           (rels : b -> Rel a) ->
                           ((m : b) -> Fixed f (rels m)) ->
                           Fixed f (IntersectionFamily rels)
intersectionFamilyClosedClosed {a} {b} f (MkClosureOperator infl incr idem) rels allFixed =
  MkEquivalent {a} (\x,y,pickrel => infl (IntersectionFamily rels) x y pickrel) yeah
    where
      yeah : (x,y : a) -> f (IntersectionFamily rels) x y -> IntersectionFamily rels x y
      yeah x y fIFrelsxy p with (allFixed p)
        yeah x y fIFrelsxy p | (MkEquivalent g z) = z x y blah
        where
          blah : f (rels p) x y
          blah = let foo = intersectionCoarserAll rels p
                 in incr (IntersectionFamily rels) (rels p) foo x y fIFrelsxy

choose : (r1, r2 : Rel a) -> Bool -> Rel a
choose r1 r2 False = r1
choose r1 r2 True = r2

intersectionClosedClosed : (f : Rel a -> Rel a) ->
                           ClosureOperator f ->
                           (rel1, rel2 : Rel a) ->
                           Fixed f rel1 ->
                           Fixed f rel2 ->
                           Fixed f (rel1 `Intersection` rel2)
intersectionClosedClosed {a} f clOpf rel1 rel2 fixedfrel1 fixedfrel2 =
  intersectionFamilyClosedClosed f clOpf (boolRel rel1 rel2) fixy
  where
    fixy : (m : Bool) -> Fixed f (boolRel rel1 rel2 m)
    fixy False = fixedfrel1
    fixy True = fixedfrel2


-- TODO This admits an obvious generalization to increasing functions,
-- and something weaker than fixedness.
closureCoarsestClosedFiner : (f : Rel a -> Rel a) ->
                             ClosureOperator f ->
                             (rel, r : Rel a) ->
                             rel `Coarser` r ->
                             Fixed f r ->
                             f rel `Coarser` r
closureCoarsestClosedFiner {a} f (MkClosureOperator infl incr idem) rel r crsrelr (MkEquivalent g h) x y frelxy =
  let frxy = incr rel r crsrelr x y frelxy
  in h x y frxy

{-
compositionClosureOps_lem : (f, g : Rel a -> Rel a) ->
                        ClosureOperator f ->
                        ClosureOperator g ->
                        ((r : Rel a) -> Fixed f r -> Fixed f (g r)) ->
                        ((r : Rel a) -> Fixed g r -> Fixed g (f r)) ->
                        (rel : Rel a) -> f (g rel) `Coarser` g (f rel)
compositionClosureOps_lem f g clOpf@(MkClosureOperator inflf incrf idemf) clOpg@(MkClosureOperator inflg incrg idemg) frfgr grgfr rel =
  let ho : (Fixed f (g (f rel)))
          = frfgr (f rel) (idemf rel)
      hum : (Fixed g (f (g rel)))
          = grgfr (g rel) (idemg rel)
      yeah : (f (g (f rel)) `Coarser` g (f rel))
          = closureCoarsestClosedFiner f clOpf (g (f rel)) (g (f rel)) (\x,y,xy => xy) ho
      righ : (g (f (g rel)) `Coarser` f (g rel))
          = closureCoarsestClosedFiner g clOpg (f (g rel)) (f (g rel)) (\x,y,xy => xy) hum
  in ?compositionClosureOps_lem_rhs
  -}

                        {-
compositionClosureOps_lem {a} f g clOpf@(MkClosureOperator inflf incrf idemf) (MkClosureOperator inflg incrg idemg) frfgr grgfr rel x y fgrelxy =
  let
    foo = closureCoarsestClosedFiner f clOpf (g rel) (g (f rel))
    relCoarserFRel = inflf rel
    grelCoarserGFRel = incrg rel (f rel) relCoarserFRel
  in ?nnneeen
  -}

