--------------------------------------------------------------------------------
-- Okasaki-style maxiphobic heaps.  See the paper:
--   ``Fun with binary heap trees'', Chris Okasaki, Fun of programming, 2003.
--------------------------------------------------------------------------------

module Data.Heap


%default total
%access export

export data MaxiphobicHeap : Type -> Type where
  Empty : MaxiphobicHeap a
  Node  : Nat -> MaxiphobicHeap a -> a -> MaxiphobicHeap a -> MaxiphobicHeap a

----------------------------------------- ---------------------------------------
-- Syntactic tests
--------------------------------------------------------------------------------

total isEmpty : MaxiphobicHeap a -> Bool
isEmpty Empty = True
isEmpty _     = False

total size : MaxiphobicHeap a -> Nat
size Empty          = Z
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
merge (Node ls ll le lr) (Node rs rl re rr) = assert_total $ -- relies on orderBySize doing the right thing
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
findMinimum Empty          Refl   impossible
findMinimum (Node s l e r) p    = e

deleteMinimum : Ord a => (h : MaxiphobicHeap a) -> (isEmpty h = False) -> MaxiphobicHeap a
deleteMinimum Empty          Refl   impossible
deleteMinimum (Node s l e r) p    = merge l r

--------------------------------------------------------------------------------
-- Conversions to and from lists (and a derived heap sorting algorithm)
--------------------------------------------------------------------------------

toList : Ord a => MaxiphobicHeap a -> List a
toList Empty          = []
toList (Node s l e r) = toList' (Node s l e r) Refl
  where
    toList' : Ord a => (h : MaxiphobicHeap a) -> (isEmpty h = False) -> List a
    toList' heap p = assert_total $ -- relies on deleteMinimum making heap smaller
          findMinimum heap p :: (Heap.toList (deleteMinimum heap p))

fromList : Ord a => List a -> MaxiphobicHeap a
fromList = foldr insert empty

sort : Ord a => List a -> List a
sort = Heap.toList . Heap.fromList

--------------------------------------------------------------------------------
-- Interface implementations
--------------------------------------------------------------------------------

implementation Show a => Show (MaxiphobicHeap a) where
  showPrec d Empty = "Empty"
  showPrec d (Node s l e r) = showCon d "Node" $ " _" ++ showArg l ++ showArg e ++ showArg r

implementation Eq a => Eq (MaxiphobicHeap a) where
  Empty              == Empty              = True
  (Node ls ll le lr) == (Node rs rl re rr) =
    ls == rs && ll == rl && le == re && lr == rr
  _                  == _                  = False

implementation Ord a => Semigroup (MaxiphobicHeap a) where
  (<+>) = merge

implementation Ord a => Monoid (MaxiphobicHeap a) where
  neutral = empty

--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

total
absurdBoolDischarge : False = True -> Void
absurdBoolDischarge Refl impossible

total
isEmptySizeZero : (h : MaxiphobicHeap a) -> (isEmpty h = True) -> size h = Z
isEmptySizeZero Empty          p = Refl
isEmptySizeZero (Node s l e r) Refl impossible

total
emptyHeapValid : Ord a => isValidHeap (empty {a}) = True
emptyHeapValid = Refl

total
singletonHeapValid : Ord a => (e : a) -> isValidHeap $ singleton e = True
singletonHeapValid e = Refl

{-
total mergePreservesValidHeaps : Ord a => (left : MaxiphobicHeap a) ->
  (right : MaxiphobicHeap a) -> (leftValid : isValidHeap left = True) ->
  (rightValid : isValidHeap right = True) -> isValidHeap $ merge left right = True
mergePreservesValidHeaps Empty              Empty              lp rp = Refl
mergePreservesValidHeaps Empty              (Node rs rl re rr) lp rp = rp
mergePreservesValidHeaps (Node ls ll le lr) Empty              lp rp = lp
mergePreservesValidHeaps (Node ls ll le lr) (Node rs rl re rr) lp rp =
  ?mergePreservesValidHeapsBody
-}



--------------------------------------------------------------------------------
-- Debug
--------------------------------------------------------------------------------

{-  XXX: poor performance when compiled, diverges when used in the REPL, but it
         does seem to work correctly!
main : IO ()
main = do
  _ <- printLn $ main.sort [10, 3, 7, 2, 9, 1, 8, 0, 6, 4, 5]
  _ <- printLn $ main.sort ["orange", "apple", "pear", "lime", "durian"]
  _ <- printLn $ main.sort [("jim", 19, "cs"), ("alice", 20, "english"), ("bob", 50, "engineering")]
  pure ()
-}
