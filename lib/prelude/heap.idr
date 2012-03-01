--------------------------------------------------------------------------------
-- Okasaki-style maxiphobic heaps.  See the paper:
--   ``Fun with binary heap trees'', Chris Okasaki, Fun of programming, 2003.
--------------------------------------------------------------------------------

module prelude.heap

import builtins

import prelude
import prelude.algebra
import prelude.list
import prelude.nat

%access public

abstract data MaxiphobicHeap : Set -> Set where
  Empty : MaxiphobicHeap a
  Node  : Nat -> MaxiphobicHeap a -> a -> MaxiphobicHeap a -> MaxiphobicHeap a

----------------------------------------- ---------------------------------------
-- Syntactic tests
--------------------------------------------------------------------------------

total isEmpty : MaxiphobicHeap a -> Bool
isEmpty Empty = True
isEmpty _     = False

total size : MaxiphobicHeap a -> Nat
size Empty          = O
size (Node s l e r) = s

isValidHeap : Ord a => MaxiphobicHeap a -> Bool
isValidHeap Empty          = True
isValidHeap (Node s l e r) =
  dominates e l && dominates e r && s == S (size l + size r)
  where
    dominates : Ord a => a -> MaxiphobicHeap a -> Bool
    dominates e Empty           = True
    dominates e (Node s l e' r) = e' <= e

--------------------------------------------------------------------------------
-- Basic heaps
--------------------------------------------------------------------------------

total empty : MaxiphobicHeap a
empty = Empty

total singleton : a -> MaxiphobicHeap a
singleton e = Node 1 Empty e Empty

--------------------------------------------------------------------------------
-- Inserting items and merging heaps
--------------------------------------------------------------------------------

private orderBySize : MaxiphobicHeap a -> MaxiphobicHeap a -> MaxiphobicHeap a ->
  (MaxiphobicHeap a, MaxiphobicHeap a, MaxiphobicHeap a)
orderBySize left centre right =
  if size left == largest then
    (left, centre, right)
  else if size centre == largest then
    (centre, left, right)
  else
    (right, left, centre)
  where
    largest : Nat
    largest = maximum (size left) $ maximum (size centre) (size right)

merge : Ord a => MaxiphobicHeap a -> MaxiphobicHeap a -> MaxiphobicHeap a
merge Empty               right             = right
merge left                Empty             = left
merge (Node ls ll le lr) (Node rs rl re rr) =
  if le < re then
    let (largest, b, c) = orderBySize ll lr (Node rs rl re rr) in
      Node mergedSize largest le (merge b c)
  else
    let (largest, b, c) = orderBySize rl rr (Node ls ll le lr) in
       Node mergedSize largest re (merge b c)
  where
    mergedSize : Nat
    mergedSize = ls + rs

insert : Ord a => a -> MaxiphobicHeap a -> MaxiphobicHeap a
insert e = merge $ singleton e

--------------------------------------------------------------------------------
-- Heap operations
--------------------------------------------------------------------------------

findMinimum : (h : MaxiphobicHeap a) -> (isEmpty h = False) -> a
findMinimum Empty          p = ?findMinimumEmptyAbsurd
findMinimum (Node s l e r) p = e

deleteMinimum : Ord a => (h : MaxiphobicHeap a) -> (isEmpty h = False) -> MaxiphobicHeap a
deleteMinimum Empty          p = ?deleteMinimumEmptyAbsurd
deleteMinimum (Node s l e r) p = merge l r

--------------------------------------------------------------------------------
-- Conversions to and from lists (and a derived heap sorting algorithm)
--------------------------------------------------------------------------------

toList : Ord a => MaxiphobicHeap a -> List a
toList Empty          = []
toList (Node s l e r) = toList' (Node s l e r) refl
  where
    toList' : Ord a => (h : MaxiphobicHeap a) -> (isEmpty h = False) -> List a
    toList' heap p = findMinimum heap p :: (toList $ deleteMinimum heap p)

fromList : Ord a => List a -> MaxiphobicHeap a
fromList = foldr insert empty

sort : Ord a => List a -> List a
sort = prelude.heap.toList . prelude.heap.fromList

--------------------------------------------------------------------------------
-- Class instances
--------------------------------------------------------------------------------

instance Show a => Show (MaxiphobicHeap a) where
  show Empty = "Empty"
  show (Node s l e r) = "Node (" ++ show l ++ " " ++ show e ++ " " ++ show r ++ ")"

instance Eq a => Eq (MaxiphobicHeap a) where
  Empty              == Empty              = True
  (Node ls ll le lr) == (Node rs rl re rr) =
    ls == rs && ll == rl && le == re && lr == rr
  _                  == _                  = False
   
instance Ord a => Semigroup (MaxiphobicHeap a) where
  (<+>) = merge

instance Ord a => Monoid (MaxiphobicHeap a) where
  neutral = empty

instance Ord a => JoinSemilattice (MaxiphobicHeap a) where
  join = merge

--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

total absurdBoolDischarge : False = True -> _|_
absurdBoolDischarge p = replace {P = disjointTy} p ()
  where
    total disjointTy : Bool -> Set
    disjointTy False  = ()
    disjointTy True   = _|_

total isEmptySizeZero : (h : MaxiphobicHeap a) -> (isEmpty h = True) -> size h = O
isEmptySizeZero Empty          p = refl
isEmptySizeZero (Node s l e r) p = ?isEmptySizeZeroNodeAbsurd

total emptyHeapValid : Ord a => isValidHeap empty = True
emptyHeapValid = refl

total singletonHeapValid : Ord a => (e : a) -> isValidHeap $ singleton e = True
singletonHeapValid e = refl

{-
total mergePreservesValidHeaps : Ord a => (left : MaxiphobicHeap a) ->
  (right : MaxiphobicHeap a) -> (leftValid : isValidHeap left = True) ->
  (rightValid : isValidHeap right = True) -> isValidHeap $ merge left right = True
mergePreservesValidHeaps Empty              Empty              lp rp = refl
mergePreservesValidHeaps Empty              (Node rs rl re rr) lp rp = rp
mergePreservesValidHeaps (Node ls ll le lr) Empty              lp rp = lp
mergePreservesValidHeaps (Node ls ll le lr) (Node rs rl re rr) lp rp =
  ?mergePreservesValidHeapsBody
-}

--------------------------------------------------------------------------------
-- Proofs
--------------------------------------------------------------------------------

isEmptySizeZeroNodeAbsurd = proof {
    intros;
    refine FalseElim;
    refine absurdBoolDischarge;
    exact p;
}

findMinimumEmptyAbsurd = proof {
    intros;
    refine FalseElim;
    refine absurdBoolDischarge;
    rewrite p;
    trivial;
}

deleteMinimumEmptyAbsurd = proof {
    intros;
    refine FalseElim;
    refine absurdBoolDischarge;
    rewrite p;
    trivial;
}

--------------------------------------------------------------------------------
-- Debug
--------------------------------------------------------------------------------

{-  XXX: poor performance when compiled, diverges when used in the REPL, but it
         does seem to work correctly!
main : IO ()
main = do
  _ <- print $ main.sort [10, 3, 7, 2, 9, 1, 8, 0, 6, 4, 5]
  _ <- print $ main.sort ["orange", "apple", "pear", "lime", "durian"]
  _ <- print $ main.sort [("jim", 19, "cs"), ("alice", 20, "english"), ("bob", 50, "engineering")]
  return ()
-}
