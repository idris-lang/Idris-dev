module Data.SortedBag

import Control.Isomorphism
import Control.Pipeline
import Data.Chain
import Data.Combinators
import Data.PosNat
import Data.SortedMap

%default total
%access export

data SortedBag k = BagWrapper (SortedMap k PosNat)

||| Remove the `BagWrapper` from a bag (the required proof from `PosNat` makes
||| this safe)
unwrapBag : SortedBag k -> SortedMap k PosNat
unwrapBag (BagWrapper m) = m

||| An `Isomorphism` between a wrapped and unwrapped bag
wrappedBagIso : Iso (SortedMap k PosNat) (SortedBag k)
wrappedBagIso = MkIso BagWrapper unwrapBag (\(BagWrapper _) => Refl) (\_ => Refl)

||| A type for converting a function from an operation over SortedMaps to an
||| operation over SortedBags
OnMapsT : Nat -> Type -> Type
OnMapsT n k = (EndoChain n $ SortedMap k PosNat) -> (EndoChain n $ SortedBag k)

||| Apply an n-ary function over the wrapped `SortedMap`.
onMaps : OnMapsT n k
onMaps = withIso wrappedBagIso

||| Special case for n=1 for `onMaps`
onMap : OnMapsT 1 k
onMap = onMaps {n=1}

||| An empty bag.
empty : Ord k => SortedBag k
empty = BagWrapper empty

||| The type of `insert` and the common core of most functions that update
||| the contests of a Bag.
UpdateBag : Type -> Type
UpdateBag k = k -> SortedBag k -> SortedBag k

-- Keep in mind:
-- Idris> the Nat $ sum Nothing
-- 0 : Nat
-- Idris> the Nat $ sum $ Just 10
-- 10 : Nat

||| Perform a count on the underlying `SortedMap`
countMap : k -> SortedMap k PosNat -> Nat
countMap k m = sum $ fst <$> lookup k m

||| Apply a function `(Nat -> Nat)` to a given argument
alterCounts : (Nat -> Nat) -> UpdateBag k
alterCounts f k = onMap $ \m => let
    n = countMap k m
    n' = f n
  in m |> if n == n'
    then id -- No change before and after.
    else case n' of
      Z => delete k
      n'@(S _) => insert k (n' ** ItIsSucc)

||| Count the number of occurances
count : k -> SortedBag k -> Nat
count k (BagWrapper m) = countMap k m

||| Is a count non-zero?
contains : k -> SortedBag k -> Bool
contains = isSucc ... count

||| insert a given number of items
insertN : Nat -> UpdateBag k
insertN n = alterCounts (plus n)

||| insert a single item.
insert : UpdateBag k
insert = alterCounts S

||| delete a given number of items
deleteN : Nat -> UpdateBag k
deleteN n = alterCounts (`minus` n)

||| delete 1 item (equivalent to `deleteN 1`)
delete1 : UpdateBag k
delete1 = deleteN 1

||| Delete all ocurances
delete : UpdateBag k
delete = alterCounts $ const Z

||| A single item (more efficient than `insert x empty`)
singleton : Ord k => k -> SortedBag k
singleton k = BagWrapper $ Data.SortedMap.insert k one empty
-- So that we don't need to do a fetch first

-- The reason for rewriting this file, because now it is
||| O(1). Are there any items? The proof in PosNat ensures that there are no
||| zero-counted items.
null : SortedBag k -> Bool
null (BagWrapper m) = null m

||| Convert a list to a Sorted Bag
fromList : Ord k => List k -> SortedBag k
fromList = foldr insert empty

||| Convert a Sorted Bag to a List, keeping it sorted.
toList : SortedBag k -> List k
toList (BagWrapper m) = concat $ (\(x, (n ** _)) => replicate n x) <$> toList m

-- TODO: more efficient, implementation also for Map and Set
Foldable SortedBag where
  foldl f zero = foldl f zero . Data.SortedBag.toList
  foldr f zero = foldr f zero . Data.SortedBag.toList

||| Merge two bags
union : EndoChain 2 (SortedBag k)
union = onMaps {n=2} merge

Semigroup (SortedBag a) where
  (<+>) = union

Ord a => Monoid (SortedBag a) where
  neutral = empty
