module Data.Nat.Views

||| View for dividing a Nat in half
public export
data Half : Nat -> Type where
     HalfOdd : {n : Nat} -> Half (S (n + n))
     HalfEven : {n : Nat} -> Half (n + n)

||| View for dividing a Nat in half, recursively
public export
data HalfRec : Nat -> Type where
     HalfRecZ : HalfRec Z
     HalfRecEven : {n : Nat} -> (rec : Lazy (HalfRec n)) -> HalfRec (n + n)
     HalfRecOdd : {n : Nat} -> (rec : Lazy (HalfRec n)) -> HalfRec (S (n + n))

||| Covering function for the `Half` view
export
half : (n : Nat) -> Half n
half Z = HalfEven {n=0}
half (S k) with (half k)
  half (S (S (n + n))) | HalfOdd = rewrite plusSuccRightSucc (S n) n in
                                           HalfEven {n=S n}
  half (S (n + n)) | HalfEven = HalfOdd

halfRecFix : (n : Nat) -> ((m : Nat) -> LT m n -> HalfRec m) -> HalfRec n
halfRecFix Z hrec = HalfRecZ
halfRecFix (S k) hrec with (half k)
  halfRecFix (S (S (n + n))) hrec | HalfOdd 
       = rewrite plusSuccRightSucc (S n) n in 
                 HalfRecEven (hrec (S n) (LTESucc (LTESucc (lteAddRight _))))
  halfRecFix (S (n + n)) hrec | HalfEven 
       = HalfRecOdd (hrec n (LTESucc (lteAddRight _)))

||| Covering function for the `HalfRec` view
export
halfRec : (n : Nat) -> HalfRec n
halfRec n = accInd halfRecFix n (ltAccessible n)

