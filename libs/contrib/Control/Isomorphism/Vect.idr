module Control.Isomorphism.Vect

import Control.Isomorphism
import Data.Vect
import Interfaces.Verified

%default total
%access public export

||| `Vect Z a` has only one value: `[]`.
nilUnit : Iso (Vect Z a) ()
nilUnit = MkIso (const ()) (const []) (\() => Refl) (\[] => Refl)

||| A `Vect (S Z) a` is just an `a`.
oneIdentity : Iso (Vect (S Z) a) a
oneIdentity = MkIso to (\x => [x]) (\x => Refl) (\[x] => Refl)
  where to : Vect 1 a -> a
        to [x] = x

||| Moves between `x :: xs` and `(x, xs)`.
consPair : Iso (Vect (S n) a) (a, Vect n a)
consPair = MkIso to (uncurry (::)) (\(x, xs) => Refl) (\(x :: xs) => Refl)
  where to : Vect (S n) a -> (a, Vect n a)
        to (x :: xs) = (x, xs)

||| An `Iso` based on `splitAt` and `(++)`.
splitPair : Iso (Vect (n + m) a) (Vect n a, Vect m a)
splitPair {n} {m} = MkIso (splitAt n) (uncurry (++)) toFrom fromTo
  where pairify : q = w -> e = r -> (q, e) = (w, r)
        pairify Refl Refl = Refl
        toFrom (ns, ms) = trans (splitAtTakeDrop n (ns ++ ms)) $ pairify (takePrefix ns ms) (dropPrefix ns ms)
        fromTo xs = rewrite splitAtTakeDrop {m} n xs in takeDropConcat n xs

||| An `Iso` based on `zip` and `unzip`.
zipped : Iso (Vect n a, Vect n b) (Vect n (a, b))
zipped = MkIso (uncurry zip) unzip toFrom (\(as, bs) => fromTo as bs)
  where toFrom : {n : Nat} -> (xs : Vect n (a, b)) -> uncurry Vect.zip (unzip xs) = xs
        toFrom [] = Refl
        toFrom ((a, b) :: xs) with (unzip xs) proof p
          | (as, bs) = cong $ trans (cong p) (toFrom xs)
        fromTo : {n : Nat} -> (as : Vect n a) -> (bs : Vect n b) -> unzip (zip as bs) = (as, bs)
        fromTo [] [] = Refl
        fromTo (a :: as) (b :: bs) = rewrite fromTo as bs in Refl

||| An `Iso` based on `zip3` and `unzip3`.
zipped3 : Iso (Vect n a, Vect n b, Vect n c) (Vect n (a, b, c))
zipped3 = MkIso (uncurrry zip3) unzip3 toFrom (\(as, bs, cs) => fromTo as bs cs)
  where uncurrry : (w -> x -> y -> z) -> ((w, x, y) -> z)
        uncurrry w (x, y, z) = w x y z
        toFrom : {n : Nat} -> (xs : Vect n (a, b, c)) -> uncurrry Vect.zip3 (unzip3 xs) = xs
        toFrom [] = Refl
        toFrom ((a, b, c) :: xs) with (unzip3 xs) proof p
          | (as, bs, cs) = cong $ trans (cong p) (toFrom xs)
        fromTo : {n : Nat} -> (as : Vect n a) -> (bs : Vect n b) -> (cs : Vect n c) -> unzip3 (zip3 as bs cs) = (as, bs, cs)
        fromTo [] [] [] = Refl
        fromTo (a :: as) (b :: bs) (c :: cs) = rewrite fromTo as bs cs in Refl

||| An `Iso` based on `transpose`.
transposition : Iso (Vect o (Vect i a)) (Vect i (Vect o a))
transposition {a} = MkIso transpose transpose prf prf
  where prf : {i : Nat} -> {o : Nat} -> (xss : Vect o (Vect i a)) -> transpose (transpose xss) = xss
        prf [] = vectMustBeNil $ transpose [| [] |]
        prf (xs :: xss) = rewrite transposeCons xs (transpose xss) in cong (prf xss)

||| Split the `Vect` every `m` elements, making `n` `Vect m a`s.
||| The result is rectangular and has the same order as the original.
|||
||| This is the inverse of `concat`.
unconcat : Vect (n * m) a -> Vect n (Vect m a)
unconcat {n = Z} [] = []
unconcat {n = S k} {m} xs with (splitAt m xs)
  | (xs', xss) = xs' :: unconcat xss
||| An `Iso` based on `unconcat` and `concat`.
|||
||| ```idris example
||| from rectangular [[1,2,3],[4,5,6]]
||| ```
rectangular : Iso (Vect (n * m) a) (Vect n (Vect m a))
rectangular = MkIso unconcat concat toFrom fromTo
  where toFrom : (xss : Vect i (Vect o a)) -> unconcat (concat xss) = xss
        toFrom {i = Z} [] = Refl
        toFrom {i = S i} {o} (xs :: xss) = rewrite splitAtTakeDrop o {m = i * o} (xs ++ concat xss) in
                                           rewrite takePrefix xs (concat xss) in
                                           rewrite dropPrefix xs (concat xss) in
                                           cong (toFrom xss)
        fromTo : (xs : Vect (i * o) a) -> concat (unconcat xs) = xs
        fromTo {i = Z} [] = Refl
        fromTo {i = S i} {o} xs = rewrite splitAtTakeDrop o {m = i * o} xs in
                                  rewrite fromTo {i} {o} (drop o xs) in
                                  takeDropConcat o xs

-- Not an Iso because (=) is not extensional, but it works in spirit
||| Go through all possible inputs and tabulate the outputs in a `Vect`.
|||
||| Or: turn a function from indices to values into a `Vect`.
||| Or: the inverse of `index`.
unindex : (Fin n -> a) -> Vect n a
unindex {n = Z} _ = []
unindex {n = S k} f = f FZ :: unindex (f . FS)

||| Indexing into the table of outputs of `f` is like calling `f` itself.
indexUnindex : (i : Fin n) -> (f : Fin n -> a) -> index i (unindex f) = f i
indexUnindex FZ _ = Refl
indexUnindex (FS k) f = rewrite indexUnindex k (f . FS) in Refl
||| Given a function `f`, a `Vect` `xs`, and a proof that calling `f` gives the same result as indexing into `xs`,
||| prove that `xs` is the table of outputs of `f`.
unindexIndex' : (xs : Vect n a) -> (f : Fin n -> a) -> ((i : Fin n) -> f i = index i xs) -> unindex f = xs
unindexIndex' [] _ _ = Refl
unindexIndex' (x :: xs) f prf = rewrite prf FZ in rewrite unindexIndex' xs (f . FS) (\i => rewrite prf $ FS i in Refl) in Refl
||| If `f` and `g` are extensionally equal (equal outputs for all inputs), then `unindex f = unindex g`.
congExtUnindex : (f : Fin n -> a) -> (g : Fin n -> a) -> ((i : Fin n) -> f i = g i) -> unindex f = unindex g
congExtUnindex f g p = unindexIndex' (unindex g) f $ \i => trans (p i) $ sym $ indexUnindex i g
||| Functions with the same tables are the same themselves.
injExtUnindex : (f : Fin n -> a) -> (g : Fin n -> a) -> unindex f = unindex g -> ((i : Fin n) -> f i = g i)
injExtUnindex f g p i = rewrite sym $ indexUnindex i f in rewrite sym $ indexUnindex i g in cong p
||| A simpler version of `unindexIndex'` which only proves that `unindex` is the inverse of `index`.
unindexIndex : (xs : Vect n a) -> unindex (\i => index i xs) = xs
unindexIndex xs = unindexIndex' xs (\i => index i xs) (\i => Refl)

||| Given a function that computes an index in the input from the index in the output, produce a `Vect o` of elements from the input.
|||
||| This is the map function of the functor `\i => Vect i a` from `\i, o => Fin o -> Fin i` to `\i, o => Vect i a -> Vect o a`.
fromIndices : (Fin o -> Fin i) -> Vect i a -> Vect o a
fromIndices f xs = unindex (flip index xs . f)
indexFromIndices : (f : Fin o -> Fin i) -> (xs : Vect i a) -> (n : Fin o) -> index n (fromIndices f xs) = index (f n) xs
indexFromIndices f xs n = indexUnindex n (\i => index (f i) xs)
fromIndicesFromIndices : (to : Fin n -> Fin n) -> (from : Fin n -> Fin n) -> (fromTo : (i : Fin n) -> from (to i) = i) -> (xs : Vect n a) -> fromIndices to (fromIndices from xs) = xs
fromIndicesFromIndices to from fromTo xs = unindexIndex' xs (\x => index (to x) (unindex (\x' => index (from x') xs))) $ \i =>
                        rewrite indexUnindex (to i) (\x' => index (from x') xs) in rewrite fromTo i in Refl

||| Given a permutation of the indices, provide an `Iso` that can permute a `Vect n` the "same" way. More precisely,
||| if the index `i` is sent to `j`, then the element at index `i` ends up at index `j` (`indexPermuted`). An
||| `Iso (Fin n) (Fin n)` represents a permutation of the integers `[0, n)` because it ensures that no elements
||| are "lost" or "duplicated".
|||
||| Note this has the *opposite* behavior to `fromIndices`. This function is more "visceral"; it can be imagined
||| as shuffling a `Vect` in the same way `map (to permutation)` shuffles `range`. Or, in more categorical terms,
||| `fromIndices` represents a contravariant functor from the category `\i, o => Fin i -> Fin o` to `\i, o => Vect i a -> Vect o a`,
||| and `permuted` represents that functor restricted to isomorphisms and made covariant with `isoSym`.
|||
||| ```idris example
||| to (permuted (stimes 2 rotatedDown)) [1, 2, 3, 4, 5] == [3, 4, 5, 1, 2]
||| to (permuted (swapped 3 0))          [1, 2, 3, 4, 5] == [4, 2, 3, 1, 5]
||| ```
|||
||| @ permutation an `Iso` representing the transformation on the indices
permuted : (permutation : Iso (Fin n) (Fin n)) -> Iso (Vect n a) (Vect n a)
-- [to, from => f from, f to] is not a typo
-- fromIndices needs a function outputIdx => inputIdx, so to "align" the "motion" of the Fins with the elements, to uses from and from uses to.
permuted (MkIso toI fromI toFromI fromToI) = MkIso (fromIndices fromI) (fromIndices toI) (fromIndicesFromIndices fromI toI toFromI) (fromIndicesFromIndices toI fromI fromToI)
permutedSym : (permutation : Iso (Fin n) (Fin n)) -> permuted (isoSym permutation) = isoSym (permuted permutation)
permutedSym (MkIso to from toFrom fromTo) = Refl
indexPermuted : (permutation : Iso (Fin n) (Fin n)) -> (i : Fin n) -> (xs : Vect n a) -> index i xs = index (to permutation i) (to (permuted permutation) xs)
indexPermuted (MkIso to from toFrom fromTo) i xs = replace {P = \xs' => index i xs' = index (to i) (fromIndices from xs) } (fromIndicesFromIndices to from fromTo xs) $
                                                   rewrite indexFromIndices to (fromIndices from xs) i in Refl
