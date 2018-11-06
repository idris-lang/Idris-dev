module Data.Fin.Extra

import Data.Fin

%access public export
%default total


||| Proof that an element **n** of Fin **m** , when converted to Nat is smaller than the bound **m**.
elemSmallerThanBound : (n : Fin m) -> LT (finToNat n) m
elemSmallerThanBound FZ = LTESucc LTEZero
elemSmallerThanBound (FS x) = LTESucc (elemSmallerThanBound x)

||| Proof that application of finToNat the last element of Fin **S n** gives **n**.
finToNatLastIsBound : finToNat (Fin.last {n}) = n
finToNatLastIsBound {n=Z} = Refl
finToNatLastIsBound {n=S k} = rewrite finToNatLastIsBound {n=k} in Refl

||| Proof that an element **n** of Fin **m** , when converted to Nat is smaller than the bound **m**.
finToNatWeakenNeutral : {n : Fin m} -> finToNat (weaken n) = finToNat n
finToNatWeakenNeutral {n=FZ} = Refl
finToNatWeakenNeutral {m=S (S _)} {n=FS _} = cong finToNatWeakenNeutral

||| Proof that it's possible to strengthen a weakened element of Fin **m**.
strengthenWeakenNeutral : (n : Fin m) -> strengthen (weaken n) = Right n
strengthenWeakenNeutral {m=S _} FZ = Refl
strengthenWeakenNeutral {m=S (S _)} (FS k) = rewrite strengthenWeakenNeutral k in Refl

||| Proof that it's not possible to strengthen the last element of Fin **n**.
strengthenLastIsLeft : strengthen (Fin.last {n}) = Left (Fin.last {n})
strengthenLastIsLeft {n=Z} = Refl
strengthenLastIsLeft {n=S k} = rewrite strengthenLastIsLeft {n=k} in Refl

||| Enumerate elements of Fin **n** backwards.
invFin : Fin n -> Fin n
invFin FZ = last
invFin {n=S (S _)} (FS k) = weaken (invFin k)

||| Proof that an inverse of a weakened element of Fin **n** is a successive of an inverse of an original element.
invWeakenIsSucc : (m : Fin n) -> invFin (weaken m) = FS (invFin m)
invWeakenIsSucc FZ = Refl
invWeakenIsSucc {n=S (S _)} (FS k) = rewrite invWeakenIsSucc k in Refl

||| Proof that double inversion of Fin **n** gives the original.
doubleInvFinSame : (m : Fin n) -> invFin (invFin m) = m
doubleInvFinSame {n=S Z} FZ = Refl
doubleInvFinSame {n=S (S k)} FZ = rewrite doubleInvFinSame {n=S k} FZ in Refl
doubleInvFinSame {n=S (S _)} (FS x) = trans (invWeakenIsSucc $ invFin x) (cong $ doubleInvFinSame x)

||| Proof that an inverse of the last element of Fin (S **n**) in FZ.
invLastIsFZ : invFin (Fin.last {n}) = FZ
invLastIsFZ {n=Z} = Refl
invLastIsFZ {n=S k} = rewrite invLastIsFZ {n=k} in Refl

||| Proof that it's possible to strengthen an inverse of a succesive element of Fin **n**.
strengthenNotLastIsRight : (m : Fin (S n)) -> strengthen (invFin (FS m)) = Right (invFin m)
strengthenNotLastIsRight m = strengthenWeakenNeutral (invFin m)

||| Either tightens the bound on a Fin or proves that it's the last.
strengthen' : (m : Fin (S n)) -> Either (m = Fin.last) (m' : Fin n ** finToNat m = finToNat m')
strengthen' {n = Z} FZ = Left Refl
strengthen' {n = S k} FZ = Right (FZ ** Refl)
strengthen' {n = S k} (FS m) with (strengthen' m)
    | Left eq   = Left $ cong eq
    | Right (m' ** eq)  = Right (FS m' ** cong eq)

||| A view of Nat as a quotient of some number and a finite remainder.
data FractionView : (n : Nat) -> (d : Nat) -> Type where
    Fraction : (n : Nat) -> (d : Nat) -> {auto ok: GT d Z} ->
                (q : Nat) -> (r : Fin d) ->
                q * d + finToNat r = n -> FractionView n d

||| Converts Nat to the fractional view with a non-zero divisor.
divMod : (n, d : Nat) -> {auto ok: GT d Z} -> FractionView n d
divMod Z (S d) = Fraction Z (S d) Z FZ Refl
divMod (S n) (S d) with (divMod n (S d))
    | (Fraction n (S d) q r eq) with (strengthen' r)
        | Left eq' = Fraction (S n) (S d) (S q) FZ $
            rewrite sym eq in
                rewrite trans (cong {f=finToNat} eq') finToNatLastIsBound in
                    cong $ trans
                        (plusZeroRightNeutral (d + q * S d))
                        (plusCommutative d (q * S d))
        | Right (r' ** eq') = Fraction (S n) (S d) q (FS r') $
            rewrite sym $ plusSuccRightSucc (q * S d) (finToNat r') in
                cong $ trans (sym $ cong {f=plus (q * S d)} eq') eq