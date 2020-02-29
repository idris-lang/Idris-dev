module Data.Nat.Parity

%access public export

----------------------------------------

-- Type-level, constructive definitions of parity.

||| A nat is Even when it is twice some other nat.
Even : Nat -> Type
Even n = (half : Nat ** n = half * 2)

||| A nat is Odd when it is one more than twice some other nat.
Odd : Nat -> Type
Odd n = (haf : Nat ** n = S $ haf * 2)

----------------------------------------

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

----------------------------------------

-- Boolean definitions of parity.

mutual
  even : Nat -> Bool
  even Z = True
  even (S k) = odd k

  odd : Nat -> Bool
  odd Z = False
  odd (S k) = even k

----------------------------------------

-- The boolean and type-level definitions are equivalent in the sense
-- that a proof of one can be gotten from a proof of the other.

mutual
  ||| Evens are even.
  evenEven : Even n -> even n = True
  evenEven {n = Z} _ = Refl
  evenEven {n = S _} pf = oddOdd $ predEvenOdd pf

  ||| Odds are odd.
  oddOdd : Odd n -> odd n = True
  oddOdd {n = Z} (_ ** pf) = absurd pf
  oddOdd {n = S _} pf = evenEven $ predOddEven pf

mutual
  ||| If it's even, it's Even.
  evenEvenConverse : even n = True -> Even n
  evenEvenConverse {n = Z} prf = (0 ** Refl)
  evenEvenConverse {n = S k} prf =
    let (haf ** pf) = oddOddConverse prf in
      (S haf ** cong pf)

  ||| If it's odd, it's Odd
  oddOddConverse : odd n = True -> Odd n
  oddOddConverse {n = Z} prf = absurd prf
  oddOddConverse {n = S k} prf =
    let (half ** pf) = evenEvenConverse prf in
      (half ** cong pf)

----------------------------------------

||| Every nat is either even or odd.
evenorodd : (n : Nat) -> Either (even n = True) (odd n = True)
evenorodd Z = Left Refl
evenorodd (S k) = case evenorodd k of
  Left l => Right l
  Right r => Left r

||| Every nat is either Even or Odd.
evenOrOdd : (n : Nat) -> Either (Even n) (Odd n)
evenOrOdd n = case evenorodd n of
  Left e => Left $ evenEvenConverse e
  Right o => Right $ oddOddConverse o

||| No nat is both even and odd.
notevenandodd : even n = True -> odd n = True -> Void
notevenandodd {n = Z} en on = absurd on
notevenandodd {n = S _} en on = notevenandodd on en

||| No nat is both Even and Odd.
notEvenAndOdd : Even n -> Odd n -> Void
notEvenAndOdd en on = notevenandodd (evenEven en) (oddOdd on)

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

----------------------------------------

||| An Odd is the successor of an Even.
oddSuccEven : Odd n -> (m : Nat ** (n = S m, Even m))
oddSuccEven (haf ** pf) = (haf * 2 ** (pf, (haf ** Refl)))

||| Even plus Even is Even.
evenPlusEven : Even j -> Even k -> Even (j + k)
evenPlusEven (half_j ** pf_j) (half_k ** pf_k) =
  (half_j + half_k **
    rewrite pf_j in
      rewrite pf_k in
        sym $ multDistributesOverPlusLeft half_j half_k 2)

||| Odd plus Even is Odd.
oddPlusEven : Odd j -> Even k -> Odd (j + k)
oddPlusEven oj ek =
  let
    (i ** (ipj, ei)) = oddSuccEven oj
    (half_ik ** eik) = evenPlusEven ei ek
      in
  (half_ik **
    rewrite ipj in
      cong {f = S} eik)

||| Even plus Odd is Odd.
evenPlusOdd : Even j -> Odd k -> Odd (j + k)
evenPlusOdd {j} {k} ej ok = rewrite plusCommutative j k in oddPlusEven ok ej

||| Odd plus Odd is Even.
oddPlusOdd : Odd j -> Odd k -> Even (j + k)
oddPlusOdd oj ok =
  let
    (i ** (ipj, ei)) = oddSuccEven oj
    (haf_ik ** oik) = evenPlusOdd ei ok
      in
  (S haf_ik **
    rewrite ipj in
      rewrite oik in
        Refl)

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
  (half_j * half_k * 2 **
    rewrite pf_j in
      rewrite pf_k in
        multShuffle half_j half_k 2)

||| Odd times Even is Even.
oddMultEven : Odd j -> Even k -> Even (j * k)
oddMultEven oj (half_k ** pf_k) =
  let
    (i ** (ipj, ei)) = oddSuccEven oj
    (half_ik ** oik) = evenMultEven ei (half_k ** pf_k)
      in
  (half_k + half_ik **
    rewrite multDistributesOverPlusLeft half_k half_ik 2 in
      rewrite ipj in
        rewrite oik in
          rewrite pf_k in
            Refl)

||| Even times Odd is Even.
evenMultOdd : Even j -> Odd k -> Even (j * k)
evenMultOdd {j} {k} ej ok = rewrite multCommutative j k in oddMultEven ok ej

||| Odd times Odd is Odd.
oddMultOdd : Odd j -> Odd k -> Odd (j * k)
oddMultOdd oj (haf_k ** pf_k) =
  let
    (i ** (ipj, ei)) = oddSuccEven oj
    (half_ik ** eik) = evenMultOdd ei (haf_k ** pf_k)
      in
  (haf_k + half_ik **
    rewrite multDistributesOverPlusLeft haf_k half_ik 2 in
      rewrite ipj in
        rewrite eik in
          rewrite pf_k in
            Refl)
