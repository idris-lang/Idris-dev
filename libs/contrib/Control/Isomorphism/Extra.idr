module Control.Isomorphism.Extra

import Control.Isomorphism
import Interfaces.Verified

%default total
%access public export

||| Form an `Iso` that is the identity for almost all inputs, except it will swap either of the arguments for the other.
||| It is the same function in both directions.
|||
||| @ l the value that will be turned into `r`
||| @ r the value that will be turned into `l`
swapped : DecEq a => (l : a) -> (r : a) -> Iso a a
swapped {a} l r = MkIso swap swap prf prf
  where swap : a -> a
        swap x = case decEq l x of { Yes _ => r; No _ => case decEq r x of { Yes _ => l; No _ => x } }
        prf : (x : a) -> swap (swap x) = x
        prf x with (decEq l x)
          | (Yes lex) with (decEq r x)
            | (Yes rex) with (decEq l r)
              | (Yes ler) = rex
              | (No lnr) = absurd $ lnr $ trans lex $ sym rex
            | (No rnx) with (decEq l r)
              | (Yes ler) = absurd $ rnx $ trans (sym ler) lex
              | (No lnr) with (decEq r r)
                | (Yes Refl) = lex
                | (No rnr) = absurd $ rnr Refl
          | (No lnx) with (decEq r x)
            | (Yes rex) with (decEq l l)
              | (Yes Refl) = rex
              | (No lnl) = absurd $ lnl Refl
            | (No rnx) with (decEq l x)
              | (Yes lex) = absurd $ lnx lex
              | (No lnx') with (decEq r x)
                | (Yes rex) = absurd $ rnx rex
                | (No rnx') = Refl

mapIso : VerifiedFunctor f => Iso a b -> Iso (f a) (f b)
mapIso {f} (MkIso to from toFrom fromTo) = MkIso (map to) (map from) (prf to from toFrom) (prf from to fromTo)
  where prf : {a : Type} -> {b : Type} -> (to : a -> b) -> (from : b -> a) -> (toFrom : (x : b) -> to (from x) = x) -> (x : f b) -> map to (map from x) = x
        prf to' from' toFrom' x = rewrite sym $ functorComposition x from' to' in functorIdentity (to' . from') toFrom' x
