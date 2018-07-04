module Control.Isomorphism.Fin

import Control.Isomorphism
import Data.Fin

%default total
%access public export

strengthenLeft : (i : Fin (S n)) -> (prf : strengthen i = Left x) -> i = Fin.last
strengthenLeft {n = Z} FZ Refl = Refl
strengthenLeft {n = S _} FZ Refl impossible
strengthenLeft {n = S k} (FS x) prf with (strengthen x) proof p
  | (Left l) = rewrite strengthenLeft x (sym p) in Refl
  | (Right r) = absurd $ leftNotRight $ sym prf
strengthenRight : (i : Fin (S n)) -> (prf : strengthen i = Right x) -> weaken x = i
strengthenRight {n = Z} FZ Refl impossible
strengthenRight {n = S _} FZ Refl = Refl
strengthenRight {n = S k} (FS x) prf with (strengthen x) proof p
  | (Left l) = absurd $ leftNotRight prf
  | (Right r) = rewrite rightInjective $ sym prf in rewrite strengthenRight x $ sym p in Refl
strengthenLast : (n : Nat) -> strengthen (last {n=n}) = Left last
strengthenLast Z = Refl
strengthenLast (S k) with (strengthen (last {n=k})) proof p
  | (Left l) = cong {f = Left . FS} $ leftInjective $ trans p $ strengthenLast k
  | (Right _) with (trans p (strengthenLast k))
    | Refl impossible
strengthenWeaken : (n : Fin k) -> strengthen (weaken n) = Right n
strengthenWeaken FZ = Refl
strengthenWeaken (FS n) with (strengthen (weaken n)) proof p
  | (Left _) with (trans p (strengthenWeaken n))
    | Refl impossible
  | (Right r) = cong {f = Right . FS} $ rightInjective $ trans p $ strengthenWeaken n

||| Sends `FZ` to `last`, and `FS x` to `x`.
rotatedDown : Iso (Fin n) (Fin n)
rotatedDown = MkIso to from toFrom fromTo
  where to : Fin k -> Fin k
        to FZ = last
        to (FS x) = weaken x
        from : Fin k -> Fin k
        from {k = Z} _ impossible
        from {k = S k} j = either (const FZ) FS $ strengthen j
        toFrom : (j : Fin k) -> to (from j) = j
        toFrom {k = S Z} FZ = Refl
        toFrom {k = S (S k)} FZ = Refl
        toFrom {k = S (S k)} (FS i) with (strengthen i) proof p
          toFrom {k = S (S k)} (FS i) | (Left l) = rewrite strengthenLeft i (sym p) in Refl
          toFrom {k = S (S k)} (FS i) | (Right r) = rewrite strengthenRight i (sym p) in Refl
        fromTo : (j : Fin k) -> from (to j) = j
        fromTo {k = S k} FZ = rewrite strengthenLast k in Refl
        fromTo (FS x) = rewrite strengthenWeaken x in Refl
||| Sends `last` to `FZ` and every other `x` to `FS x`.
rotatedUp : Iso (Fin n) (Fin n)
rotatedUp = isoSym rotatedDown
