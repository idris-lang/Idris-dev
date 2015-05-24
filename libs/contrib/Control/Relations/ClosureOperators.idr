||| General definitions and theorems about relations
module Control.Relations.ClosureOperators
import Control.Relations.Basics

%default total
%access public

||| A closure operator on relations is one that is inflationary,
||| increasing, and idempotent.
record ClosureOperator (f : Rel a -> Rel a) where
  constructor MkClosureOperator
  infl : Inflationary f
  incr : Increasing f
  idem : Idempotent f

closureOperatorPreservesEquiv : (f : Rel a -> Rel a) ->
                                ClosureOperator f ->
                                (r1, r2 : Rel a) ->
                                r1 `Equivalent` r2 ->
                                f r1 `Equivalent` f r2

closureOperatorPreservesEquiv {a} f clOpf r1 r2 (MkEquivalent this that) =
  MkEquivalent what now
  where
    what : (x : a) -> (y : a) -> f r1 x y -> f r2 x y
    what x y fr1xy = incr clOpf r1 r2 this x y fr1xy

    now : (x : a) -> (y : a) -> f r2 x y -> f r1 x y
    now x y fr2xy = incr clOpf r2 r1 that x y fr2xy


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

closureCoarsestClosedFiner : (f : Rel a -> Rel a) ->
                             ClosureOperator f ->
                             (rel, r : Rel a) ->
                             rel `Coarser` r ->
                             Fixed f r ->
                             f rel `Coarser` r
closureCoarsestClosedFiner {a} f (MkClosureOperator infl incr idem) rel r crsrelr (MkEquivalent g h) x y frelxy =
  let frxy = incr rel r crsrelr x y frelxy
  in h x y frxy

compositionInflInfl : (f, g : Rel a -> Rel a) ->
                      Inflationary f ->
                      Inflationary g ->
                      Inflationary (f . g)
compositionInflInfl f g inflf inflg rel x y xy = inflf (g rel) x y (inflg rel x y xy)

compositionIncrIncr : (f, g : Rel a -> Rel a) ->
                      Increasing f ->
                      Increasing g ->
                      Increasing (f . g)
compositionIncrIncr f g incrf incrg rel1 rel2 r1coarserr2 =
  incrf (g rel1) (g rel2) (incrg rel1 rel2 r1coarserr2)

compositionIdem : (f, g : Rel a -> Rel a) ->
                  Idempotent f ->
                  Idempotent g ->
                  ((r : Rel a) -> Fixed f r -> Fixed f (g r)) ->
                  ((r : Rel a) -> Fixed g r -> Fixed g (f r)) ->
                  Idempotent (f . g)
compositionIdem f g idemf idemg frfgr grgfr rel =
          let fixedggrel : (Fixed g (g rel))
                          = idemg rel
              fixedgfgrel : (Fixed g (f (g rel)))
                   = grgfr (g rel) fixedggrel
              fixedfgfgrel : (Fixed f (g (f (g rel))))
                  = frfgr (f (g rel)) (idemf (g rel))
          in trns equivalentIsEquivalence _ _ _ fixedgfgrel fixedfgfgrel

closureOpsFixCoarser : (f, g : Rel a -> Rel a) ->
                       ClosureOperator f ->
                       ClosureOperator g ->
                       ((rel : Rel a) -> Fixed f rel -> Fixed g rel) ->
                       (rel : Rel a) -> g rel `Coarser` f rel
closureOpsFixCoarser f g clOpf clOpg fixedfg rel x y grelxy =
  let
    relCoarserfrel : (rel `Coarser` f rel) = infl clOpf rel
    grelCoarsergfrel : (g rel `Coarser` g (f rel)) = incr clOpg rel (f rel) relCoarserfrel
    gfrelxy : (g (f rel) x y) = grelCoarsergfrel x y grelxy
    frelFixedf : (Fixed f (f rel)) = idem clOpf rel
    frelFixedg : (Fixed g (f rel)) = fixedfg (f rel) frelFixedf
  in case frelFixedg of MkEquivalent _ from => from x y gfrelxy

||| If two closure operators *fix* the same relations, then they act the
||| same on *all* relations.
closureOpsFixSameEquiv : (f, g : Rel a -> Rel a) ->
                         ClosureOperator f ->
                         ClosureOperator g ->
                         ((rel : Rel a) -> Fixed f rel -> Fixed g rel) ->
                         ((rel : Rel a) -> Fixed g rel -> Fixed f rel) ->
                         (rel : Rel a) -> f rel `Equivalent` g rel
closureOpsFixSameEquiv f g clOpf clOpg fixedfg fixedgf rel =
  MkEquivalent (closureOpsFixCoarser g f clOpg clOpf fixedgf rel)
               (closureOpsFixCoarser f g clOpf clOpg fixedfg rel)


||| If `f` and `g` are closure operators, whenever a relation `r` is fixed under `f`,
||| `g r` is also fixed under `f`, and the other way around, then `f . g` is a closure
||| operator.
compositionClosureOps_closure : (f, g : Rel a -> Rel a) ->
                        ClosureOperator f ->
                        ClosureOperator g ->
                        ((r : Rel a) -> Fixed f r -> Fixed f (g r)) ->
                        ((r : Rel a) -> Fixed g r -> Fixed g (f r)) ->
                        ClosureOperator (f . g)
compositionClosureOps_closure {a} f g clOpf clOpg frfgr grgfr = MkClosureOperator inflfg incrfg idemfg
  where
    incrfg : Increasing (f . g)
    incrfg = compositionIncrIncr f g (incr clOpf) (incr clOpg)
    idemfg : Idempotent (f . g)
    idemfg = compositionIdem f g (idem clOpf) (idem clOpg) frfgr grgfr
    inflfg : Inflationary (f . g)
    inflfg = compositionInflInfl f g (infl clOpf) (infl clOpg)

closureOpsComm_lem : (f, g : Rel a -> Rel a) ->
                 ClosureOperator f ->
                 ClosureOperator g ->
                 ((r : Rel a) -> Fixed f r -> Fixed f (g r)) ->
                 ((r : Rel a) -> Fixed g r -> Fixed g (f r)) ->
                 (rel : Rel a) -> Fixed (f . g) rel -> Fixed (g . f) rel
closureOpsComm_lem f g clOpf clOpg frfgr grgfr rel fixedfgrel =
  let
    clOpgf = compositionClosureOps_closure g f clOpg clOpf grgfr frfgr
    foo : ( (g . f) rel `Equivalent` (g . f . f . g) rel )
        = closureOperatorPreservesEquiv (g . f) clOpgf _ _ fixedfgrel
    bar : ( (f . f . g) rel `Equivalent` (f . g) rel )
        = symm equivalentIsEquivalence _ _ (idem clOpf (g rel))
    baz : ( (g . f . f . g) rel `Equivalent` (g . f . g) rel )
        = closureOperatorPreservesEquiv g clOpg _ _ bar
    quux : ( (g . f) rel `Equivalent` (g . f . g) rel )
         = trns equivalentIsEquivalence _ _ _ foo baz
    quux' : ( (g . f . g) rel `Equivalent` (g . f) rel )
         = symm equivalentIsEquivalence _ _ quux
    fixedggrel : (Fixed g (g rel))
                = idem clOpg rel
    fixedgfgrel : ( (f . g) rel `Equivalent` (g . f . g) rel )
                = grgfr (g rel) fixedggrel
    hoop : ( rel `Equivalent` (g . f . g) rel )
         = trns equivalentIsEquivalence _ _ _ fixedfgrel fixedgfgrel
  in trns equivalentIsEquivalence _ _ _ hoop quux'

||| Two sufficiently compatible closure operators commute with each other.
closureOpsComm : (f, g : Rel a -> Rel a) ->
                 ClosureOperator f ->
                 ClosureOperator g ->
                 ((r : Rel a) -> Fixed f r -> Fixed f (g r)) ->
                 ((r : Rel a) -> Fixed g r -> Fixed g (f r)) ->
                 (rel : Rel a) -> f (g rel) `Equivalent` g (f rel)
closureOpsComm {a} f g clOpf clOpg frfgr grgfr rel =
  let clOpfg : (ClosureOperator (f . g))
             = compositionClosureOps_closure f g clOpf clOpg frfgr grgfr
      clOpgf : (ClosureOperator (g . f))
             = compositionClosureOps_closure g f clOpg clOpf grgfr frfgr
      fixedfg : ((r : Rel a) -> Fixed (f . g) r -> Fixed (g . f) r)
              = closureOpsComm_lem {a} f g clOpf clOpg frfgr grgfr
      fixedgf : ((r : Rel a) -> Fixed (g . f) r -> Fixed (f . g) r)
              = closureOpsComm_lem {a} g f clOpg clOpf grgfr frfgr
  in closureOpsFixSameEquiv (f . g) (g . f) clOpfg clOpgf fixedfg fixedgf rel
