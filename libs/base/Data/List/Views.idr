module Data.List.Views

import Data.List

-- First list is smaller than the second
smaller : List a -> List a -> Type
smaller xs ys = LT (length xs) (length ys)

-- Some proofs to help us out with recursion later
ltS : LTE (S x) y -> LTE x y
ltS (LTESucc x) = lteSuccRight x

total
ltTrans : LTE n m -> LTE m p -> LTE n p
ltTrans LTEZero y = LTEZero
ltTrans (LTESucc x) (LTESucc y) = LTESucc (ltTrans x y)

ltZimpossible : (x : smaller xs []) -> Accessible smaller xs
ltZimpossible LTEZero impossible
ltZimpossible (LTESucc _) impossible

total
smallerAcc : (ys : List a) -> smaller xs ys -> Accessible smaller xs
smallerAcc [] x = ltZimpossible x
smallerAcc (y :: ys) (LTESucc x) 
     = Access (\val, p => smallerAcc ys (ltTrans p x))

lengthSuc : (xs : List a) -> (y : a) -> (ys : List a) ->
            length (xs ++ (y :: ys)) = S (length (xs ++ ys))
lengthSuc [] _ _ = Refl
lengthSuc (x :: xs) y ys = cong (lengthSuc xs y ys)

lengthLT : (xs : List a) -> (ys : List a) -> 
           LTE (length xs) (length (ys ++ xs))
lengthLT xs [] = lteRefl
lengthLT xs (x :: ys) = lteSuccRight (lengthLT _ _)

smallerLeft : (ys : List a) -> (y : a) -> (zs : List a) -> 
              LTE (S (S (length ys))) (S (length (ys ++ (y :: zs))))
smallerLeft [] y zs = LTESucc (LTESucc LTEZero)
smallerLeft (z :: ys) y zs = LTESucc (smallerLeft ys _ _)

smallerRight : (ys : List a) -> (zs : List a) -> 
               LTE (S (S (length zs))) (S (length (ys ++ (y :: zs))))
smallerRight {y} ys zs = rewrite lengthSuc ys y zs in 
                                 (LTESucc (LTESucc (lengthLT _ _)))

||| View for splitting a list in half, non-recursively
public export
data Split : List a -> Type where
     SplitNil : Split []
     SplitOne : Split [x]
     SplitPair : Split (x :: xs ++ y :: ys)

splitHelp : (head : a) ->
            (xs : List a) -> 
            (counter : List a) -> Split (head :: xs)
splitHelp head [] counter = SplitOne
splitHelp head (x :: xs) [] = SplitPair {xs = []} {ys = xs}
splitHelp head (x :: xs) [y] = SplitPair {xs = []} {ys = xs}
splitHelp head (x :: xs) (_ :: _ :: ys) 
    = case splitHelp head xs ys of
           SplitOne => SplitPair {xs = []} {ys = []}
           SplitPair {xs} {ys} => SplitPair {xs = (x :: xs)} {ys = ys}

||| Covering function for the `Split` view
export
split : (xs : List a) -> Split xs
split [] = SplitNil
split (x :: xs) = splitHelp x xs xs

||| View for splitting a list in half, recursively
|||
||| This allows us to define recursive functions which repeatedly split lists
||| in half, with base cases for the empty and singleton lists.
public export
data SplitRec : List a -> Type where
     SplitRecNil : SplitRec []
     SplitRecOne : SplitRec [x]
     SplitRecPair : Lazy (SplitRec xs) -> Lazy (SplitRec ys) -> SplitRec (xs ++ ys)

total
splitRecFix : (xs : List a) -> ((ys : List a) -> smaller ys xs -> SplitRec ys) -> 
              SplitRec xs
splitRecFix xs srec with (split xs)
  splitRecFix [] srec | SplitNil = SplitRecNil
  splitRecFix [x] srec | SplitOne = SplitRecOne
  splitRecFix (x :: (ys ++ (y :: zs))) srec | SplitPair 
      = let left = srec (x :: ys) (smallerLeft ys y zs)
            right = srec (y :: zs) (smallerRight ys zs) in
            SplitRecPair left right

||| Covering function for the `SplitRec` view
export total
splitRec : (xs : List a) -> SplitRec xs
splitRec [] = SplitRecNil
splitRec (x :: xs) = accInd splitRecFix (x :: xs) (smallerAcc (x :: x :: xs) lteRefl)

||| View for traversing a list backwards
public export
data SnocList : List a -> Type where
     Empty : SnocList []
     Snoc : SnocList xs -> SnocList (xs ++ [x])

snocListHelp : SnocList xs -> (ys : List a) -> SnocList (xs ++ ys)
snocListHelp {xs} x [] = rewrite appendNilRightNeutral xs in x
snocListHelp {xs} x (y :: ys) 
   = rewrite appendAssociative xs [y] ys in snocListHelp (Snoc x {x=y}) ys

||| Covering function for the `SnocList` view
export
snocList : (xs : List a) -> SnocList xs
snocList xs = snocListHelp Empty xs




