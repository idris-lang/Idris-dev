module Data.Nat.Parity

%access public export

--------------------------------------------------------------------------------
-- Parity
--------------------------------------------------------------------------------

mutual
  even : Nat -> Bool
  even Z = True
  even (S k) = odd k

  odd : Nat -> Bool
  odd Z = False
  odd (S k) = even k

||| A nat is Even when it is twice some other nat.
Even : Nat -> Type
Even n = (half : Nat ** n = half * 2)

||| A nat is Odd when it is one more than twice some other nat.
Odd : Nat -> Type
Odd n = (haf : Nat ** n = S $ haf * 2)

||| Two more than an Even is Even.
add2Even : Even n -> Even (2 + n)
add2Even (half ** pf) = (S half ** cong {f = (+) 2} pf)

||| Two more than an Odd is Odd.
add2Odd : Odd n -> Odd (2 + n)
add2Odd (haf ** pf) = (S haf ** cong {f = (+) 2} pf)

||| One more than an Even is Odd.
succEvenOdd : Even n -> Odd (S n)
succEvenOdd (half ** pf) = (half ** cong {f = S} pf)

||| One more than an Odd is Even.
succOddEven : Odd n -> Even (S n)
succOddEven (haf ** pf) = (S haf ** cong {f = S} pf)

||| One less than an Odd is Even.
predOddEven : Odd (S n) -> Even n
predOddEven (haf ** pf) = (haf ** cong {f = Nat.pred} pf)

||| A helper fact.
succDoublePredPred : S n = k * 2 -> n = S $ (pred k) * 2
succDoublePredPred {k = Z} prf = absurd prf
succDoublePredPred {k = S _} prf = cong {f = Nat.pred} prf

||| One less than an Even is Odd.
predEvenOdd : Even (S n) -> Odd n
predEvenOdd (half ** pf) = (pred half ** succDoublePredPred pf)

||| Every nat is either Even or Odd.
evenOrOdd : (n : Nat) -> Either (Even n) (Odd n)
evenOrOdd Z = Left (0 ** Refl)
evenOrOdd (S k) = case evenOrOdd k of
  Left (half ** pf) => Right (half ** cong {f = S} pf)
  Right (haf ** pf) => Left (S haf ** cong {f = S} pf)

||| No nat is both Even and Odd.
notEvenAndOdd : Even n -> Odd n -> Void
notEvenAndOdd {n = Z} _ (_ ** odd) = absurd odd
notEvenAndOdd {n = (S k)} (half ** even) (haf ** odd) =
  notEvenAndOdd {n = k}
   (haf ** cong {f = Nat.pred} odd)
   (pred half ** succDoublePredPred even)

||| Evenness is decidable.
evenDec : (n : Nat) -> Dec $ Even n
evenDec n = case evenOrOdd n of
  Left even => Yes even
  Right odd => No $ \even => notEvenAndOdd even odd

||| Oddness is decidable.
oddDec : (n : Nat) -> Dec $ Odd n
oddDec n = case evenOrOdd n of
  Left even => No $ notEvenAndOdd even
  Right odd => Yes odd

mutual
  ||| Evens are even.
  evenEven : Even n -> even n = True
  evenEven {n = Z} _ = Refl
  evenEven {n = S _} pf = oddOdd $ predEvenOdd pf

  ||| Odds are odd.
  oddOdd : Odd n -> odd n = True
  oddOdd {n = Z} (_ ** pf) = absurd pf
  oddOdd {n = S _} pf = evenEven $ predOddEven pf

||| Even plus Even is Even.
evenPlusEven : Even j -> Even k -> Even (j + k)
evenPlusEven (half_j ** pf_j) (half_k ** pf_k) =
  rewrite pf_j in
    rewrite pf_k in
      (half_j + half_k **
        sym $ multDistributesOverPlusLeft half_j half_k 2)

||| Odd plus Odd is Even.
oddPlusOdd : Odd j -> Odd k -> Even (j + k)
oddPlusOdd (haf_j ** pf_j) (haf_k ** pf_k) =
  rewrite pf_j in
    rewrite pf_k in
      rewrite sym $ plusSuccRightSucc (haf_j * 2) (haf_k * 2) in
        rewrite sym $ multDistributesOverPlusLeft haf_j haf_k 2 in
          (S (haf_j + haf_k) ** Refl)

||| Even plus Odd is Odd.
evenPlusOdd : Even j -> Odd k -> Odd (j + k)
evenPlusOdd (half_j ** pf_j) (haf_k ** pf_k) =
  rewrite pf_j in
    rewrite pf_k in
      rewrite sym $ plusSuccRightSucc (half_j * 2) (haf_k * 2) in
        rewrite sym $ multDistributesOverPlusLeft half_j haf_k 2 in
          (half_j + haf_k ** Refl)

||| A helper fact.
multShuffle : (a, b, c : Nat) ->
  (a * c) * (b * c) = ((a * b) * c) * c
multShuffle a b c =
  rewrite multAssociative (a * c) b c in
    rewrite multCommutative (a * c) b in
      rewrite multAssociative b a c in
        rewrite multCommutative b a in
          Refl

||| Even times Even is Even.
evenMultEven : Even j -> Even k -> Even (j * k)
evenMultEven (half_j ** pf_j) (half_k ** pf_k) =
  rewrite pf_j in
    rewrite pf_k in
      (half_j * half_k * 2 **
        multShuffle half_j half_k 2)

||| Even times Odd is Even.
evenMultOdd : Even j -> Odd k -> Even (j * k)
evenMultOdd (half_j ** pf_j) (haf_k ** pf_k) =
  let half = half_j * haf_k * 2 in
    rewrite pf_j in
      rewrite pf_k in
        rewrite multRightSuccPlus (half_j * 2) (haf_k * 2) in
          rewrite multShuffle half_j haf_k 2 in
            (half_j + half **
              sym $ multDistributesOverPlusLeft half_j half 2)

||| Odd times Odd is Odd.
oddMultOdd : Odd j -> Odd k -> Odd (j * k)
oddMultOdd (haf_j ** pf_j) (haf_k ** pf_k) =
  let
    haf = haf_j * haf_k * 2
    rem = haf_j + haf_k
      in
  rewrite pf_j in
    rewrite pf_k in
      rewrite multRightSuccPlus (haf_j * 2) (haf_k * 2) in
        rewrite multShuffle haf_j haf_k 2 in
          rewrite plusAssociative (haf_k * 2) (haf_j * 2) (haf * 2) in
            rewrite sym $ multDistributesOverPlusLeft haf_k haf_j 2 in
              rewrite plusCommutative haf_k haf_j in
                rewrite sym $ multDistributesOverPlusLeft rem haf 2 in
                  (rem + haf ** Refl)
