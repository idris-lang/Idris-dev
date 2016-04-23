module Data.Vect.Views

import Data.Vect

||| View for traversing a vector backwards
public export
data SnocVect : Vect n a -> Type where
     Empty : SnocVect []
     Snoc : {x : a} -> {xs : Vect n a} ->
            (rec : SnocVect xs) -> SnocVect (xs ++ [x])

snocVectHelp : {xs : Vect n a} ->
               SnocVect xs -> (ys : Vect m a) -> SnocVect (xs ++ ys)
snocVectHelp {xs} x [] = rewrite vectNilRightNeutral xs in x
snocVectHelp {xs} x (y :: ys) 
    = rewrite vectAppendAssociative xs [y] ys in 
              snocVectHelp (Snoc x {x=y}) ys
                             
||| Covering function for the `SnocVect` view
||| Constructs the view in linear time
export
snocVect : (xs : Vect n a) -> SnocVect xs
snocVect xs = snocVectHelp Empty xs

||| View for splitting a vector in half, non-recursively
public export
data Split : Vect n a -> Type where
     SplitNil : Split []
     SplitOne : Split [x]
     SplitPair : {x, y : a} -> {xs : Vect n a} -> {ys : Vect m a} ->
                 Split (x :: xs ++ y :: ys)

splitHelp : (head : a) ->
            (xs : Vect n a) -> 
            (counter : Vect m a) -> Split (head :: xs)
splitHelp head [] counter = SplitOne
splitHelp head (x :: xs) [] = SplitPair {xs = []} {ys = xs}
splitHelp head (x :: xs) [y] = SplitPair {xs = []} {ys = xs}
splitHelp head (x :: xs) (_ :: _ :: ys) 
     = case splitHelp head xs ys of
            SplitOne => SplitPair {xs = []} {ys = []}
            SplitPair {xs} {ys} => SplitPair {xs = x :: xs} {ys}

||| Covering function for the `Split` view
||| Constructs the view in linear time
export
split : (xs : Vect n a) -> Split xs
split [] = SplitNil
split (x :: xs) = splitHelp x xs xs

||| View for splitting a vector in half, recursively
|||
||| This allows us to define recursive functions which repeatedly split vectors
||| in half, with base cases for the empty and singleton lists.
public export
data SplitRec : Vect n a -> Type where
     SplitRecNil : SplitRec []
     SplitRecOne : {x : a} -> SplitRec [x]
     SplitRecPair : {xs : Vect n a} -> 
                    {ys : Vect m a} -> -- Explicit, don't erase
                    (lrec : Lazy (SplitRec xs)) -> 
                    (rrec : Lazy (SplitRec ys)) -> SplitRec (xs ++ ys)

smallerPlus : LTE (S (S m)) (S (plus m (S k)))
smallerPlus {m} {k} = rewrite sym (plusSuccRightSucc m k) in 
                              (LTESucc (LTESucc (lteAddRight _)))

smallerPlus' : LTE (S (S k)) (S (plus m (S k)))
smallerPlus' {m} {k} = rewrite sym (plusSuccRightSucc m k) in 
                               LTESucc (LTESucc (rewrite plusCommutative m k in (lteAddRight _)))

||| Covering function for the `SplitRec` view
||| Constructs the view in O(n lg n)
export
splitRec : (xs : Vect n a) -> SplitRec xs
splitRec {n} input with (ltAccessible n)
  splitRec input | acc with (split input)
    splitRec [] | acc | SplitNil = SplitRecNil
    splitRec [x] | acc | SplitOne = SplitRecOne
    splitRec (x :: (xs ++ (y :: ys))) | (Access rec) | SplitPair 
        = let left = splitRec (x :: xs) | rec _ smallerPlus
              right = splitRec (y :: ys) | rec _ smallerPlus' in
              SplitRecPair left right
