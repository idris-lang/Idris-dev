module Data.List.Views

import Data.List
import Data.Nat.Views

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
     SplitPair : {x, y : a} -> {xs, ys : List a} -> -- Explicit, don't erae
                 Split (x :: xs ++ y :: ys)

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
||| Constructs the view in linear time
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
     SplitRecOne : {x : a} -> SplitRec [x]
     SplitRecPair : {lefts, rights : List a} -> -- Explicit, don't erase
                    (lrec : Lazy (SplitRec lefts)) -> 
                    (rrec : Lazy (SplitRec rights)) -> SplitRec (lefts ++ rights)

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
||| Constructs the view in O(n lg n)
export total
splitRec : (xs : List a) -> SplitRec xs
splitRec xs = accInd splitRecFix xs (smallerAcc xs)

||| View for traversing a list backwards
public export
data SnocList : List a -> Type where
     Empty : SnocList []
     Snoc : {x : a} -> {xs : List a} -> -- Explicit, so don't erase
            (rec : SnocList xs) -> SnocList (xs ++ [x])

snocListHelp : SnocList xs -> (ys : List a) -> SnocList (xs ++ ys)
snocListHelp {xs} x [] = rewrite appendNilRightNeutral xs in x
snocListHelp {xs} x (y :: ys) 
   = rewrite appendAssociative xs [y] ys in snocListHelp (Snoc x) ys

||| Covering function for the `SnocList` view
||| Constructs the view in linear time
export
snocList : (xs : List a) -> SnocList xs
snocList xs = snocListHelp Empty xs

||| View for recursively filtering a list by a predicate, applied to the
||| first item in each recursively filtered list
public export
data Filtered : (a -> a -> Bool) -> List a -> Type where
     FNil : Filtered p []
     FRec : (lrec : Lazy (Filtered p (filter (\y => p y x) xs))) -> 
            (rrec : Lazy (Filtered p (filter (\y => not (p y x)) xs))) ->
            Filtered p (x :: xs)

filteredLOK : (p : a -> a -> Bool) -> (x : a) -> (xs : List a) -> smaller (filter (\y => p y x) xs) (x :: xs)
filteredLOK p x xs = LTESucc (filterSmaller xs)

filteredROK : (p : a -> a -> Bool) -> (x : a) -> (xs : List a) -> smaller (filter (\y => not (p y x)) xs) (x :: xs)
filteredROK p x xs = LTESucc (filterSmaller xs)

||| Covering function for the `Filtered` view
||| Constructs the view in O(n lg n)
export
filtered : (p : a -> a -> Bool) -> (xs : List a) -> Filtered p xs
filtered p inp with (smallerAcc inp)
  filtered p [] | with_pat = FNil
  filtered p (x :: xs) | (Access xsrec) 
      =  FRec (filtered p (filter (\y => p y x) xs) | xsrec _ (filteredLOK p x xs))
              (filtered p (filter (\y => not (p y x)) xs) | xsrec _ (filteredROK p x xs))

lenImpossible : (n = Z) -> (n = ((S k) + right)) -> Void
lenImpossible {n = Z} _ Refl impossible
lenImpossible {n = (S _)} Refl _ impossible

total
lsplit : (xs : List a) ->
         (n : Nat) -> (n = length xs) ->
         (left, right : Nat) -> (n = left + right) ->
         (ls : List a ** rs : List a ** 
               (length ls = left, length rs = right, xs = ls ++ rs))
lsplit xs n prf Z right prf1 = ([] ** xs ** (Refl, rewrite sym prf in prf1, Refl))
lsplit [] n prf (S k) right prf1 = void $ lenImpossible prf prf1
lsplit (x :: xs) (S k) prf (S l) right prf1 
     = let (lsrec' ** rsrec' ** (lprf, rprf, recprf)) 
                = lsplit xs k (succInjective _ _ prf) l right (succInjective _ _ prf1) in
           (x :: lsrec' ** rsrec' ** (eqSucc _ _ lprf, rprf, rewrite recprf in Refl))
lsplit (_ :: _) Z Refl (S _) _ _ impossible

||| Proof that two numbers differ by at most one
public export
data Balanced : Nat -> Nat -> Type where
     BalancedZ : Balanced Z Z
     BalancedL : Balanced (S Z) Z
     BalancedRec : Balanced n m -> Balanced (S n) (S m)

||| View of a list split into two halves
|||
||| The lengths of the lists are guaranteed to differ by at most one
public export
data SplitBalanced : List a -> Type where
     MkSplitBal : {xs, ys : List a} ->
                  Balanced (length xs) (length ys) -> SplitBalanced (xs ++ ys)

mkBalancedL : n = S x -> m = x -> Balanced n m
mkBalancedL {m = Z} Refl Refl = BalancedL
mkBalancedL {m = (S k)} Refl Refl = BalancedRec (mkBalancedL Refl Refl)

mkBalanced : n = x -> m = x -> Balanced n m
mkBalanced {n = Z} Refl Refl = BalancedZ
mkBalanced {n = (S _)} {m = Z} Refl Refl impossible
mkBalanced {n = (S k)} {m = (S k)} Refl Refl = BalancedRec (mkBalanced Refl Refl)

splitBalancedLen : (xs : List a) -> (n : Nat) -> (n = length xs) -> SplitBalanced xs
splitBalancedLen xs n prf with (half n)
  splitBalancedLen xs (S (x + x)) prf | HalfOdd 
      = let (xs' ** ys' ** (lprf, rprf, apprf)) =
              lsplit xs (S (x + x)) prf (S x) x Refl in
              rewrite apprf in (MkSplitBal (mkBalancedL lprf rprf))
  splitBalancedLen xs (x + x) prf | HalfEven 
      = let (xs' ** ys' ** (lprf, rprf, apprf)) =
              lsplit xs (x + x) prf x x Refl in
              rewrite apprf in (MkSplitBal (mkBalanced lprf rprf))

||| Covering function for the `SplitBalanced`
|||
||| Constructs the view in linear time
export
splitBalanced : (xs : List a) -> SplitBalanced xs
splitBalanced xs = splitBalancedLen xs (length xs) Refl
  
||| The `VList` view allows us to recurse on the middle of a list,
||| inspecting the front and back elements simultaneously.
public export
data VList : List a -> Type where
     VNil : VList []
     VOne : VList [x]
     VCons : {x : a} -> {y : a} -> .{xs : List a} -> 
             (rec : VList xs) -> VList (x :: xs ++ [y])

total
balRec : (zs, xs : List a) ->
         Balanced (S (length zs)) (S (length xs)) -> 
         Balanced (length zs) (length xs)
balRec zs xs (BalancedRec x) = x

lengthSnoc : (x : _) -> (xs : List a) -> length (xs ++ [x]) = S (length xs) 
lengthSnoc x [] = Refl
lengthSnoc x (_ :: xs) = cong (lengthSnoc x xs)

Uninhabited (Balanced Z (S k)) where
    uninhabited BalancedZ impossible
    uninhabited BalancedL impossible
    uninhabited (BalancedRec _) impossible

toVList : (xs : List a) -> SnocList ys -> 
          Balanced (length xs) (length ys) -> VList (xs ++ ys)
toVList [] Empty y = VNil
toVList [x] Empty BalancedL = VOne
toVList (z :: zs) (Snoc {xs} {x} srec) prf
    = rewrite appendAssociative zs xs [x] in
              VCons (toVList zs srec (balRec zs xs 
                    (rewrite sym $ lengthSnoc x xs in prf)))
toVList [] (Snoc {xs} {x} _) prf 
     = let prf' : Balanced Z (S (length xs)) = rewrite sym $ lengthSnoc x xs in prf in
           absurd prf'
      
||| Covering function for `VList`
||| Constructs the view in linear time.
export
vList : (xs : List a) -> VList xs
vList xs with (splitBalanced xs)
  vList (ys ++ zs) | (MkSplitBal prf) 
        = toVList ys (snocList zs) prf

