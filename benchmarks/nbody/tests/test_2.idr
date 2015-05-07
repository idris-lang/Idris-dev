module Main

import Data.Floats
--import Effect.State
import Data.Fin
import Data.Vect
import Data.Vect.Quantifiers
import Decidable.Equality

nums : Vect 5 Nat
nums = [4,5,6,7,8]

--s_help : Fin (length nums) -> Fin (length nums)  
--s_help i = if (finToNat i) == length nums - 1
--            then i
--            else FS i

--my_sum : Fin (length nums) -> Nat -> Nat
--my_sum (last) v = v
--my_sum (length nums + n) = my_sum' (length nums + n) 

ix : Nat 
ix = length nums

my_sum' : Fin (length nums) -> Nat -> Nat
my_sum' i v = if i == fromNat (ix - 1)
                 then v
                 else my_sum' (succ i) (p + v) where p = index i nums

--my_sum' i v = my_sum' (succ i) (p + v) where p = index i nums


main : Nat
main = my_sum' 0 0

{-
vectLengthConv : m = n -> Vect m a = Vect n a
vectLengthConv prf =
  let prf' = cong {f = Vect} prf
  in cong {f = \q => q a} prf'

splitToSnocVect' : .(n : Nat) -> .(xs : Vect m a) -> .(m = n+1) -> Split n xs -> SnocVect xs
splitToSnocVect' {a} n (ys ++ zs) prf (MkSplit {k} ys zs) with (vectLengthConv {a} (plusLeftCancel n k 1 prf))
  splitToSnocVect' {a = a} n (ys ++ []) prf (MkSplit {k = Z} ys []) | Refl impossible
  splitToSnocVect' {a = a} n (ys ++ (z :: [])) prf (MkSplit {k = (S Z)} ys (z :: [])) | with_pat =
    Snoc ys z
  splitToSnocVect' {a = a} n (ys ++ (z :: (x :: xs))) prf (MkSplit {k = (S (S k))} ys (z :: (x :: xs))) | Refl impossible

splitToSnocVect : .{n : Nat} -> .{xs : Vect (S n) a} -> Split n xs -> SnocVect xs
splitToSnocVect {n} {xs} splt = splitToSnocVect' n xs (plusCommutative 1 n) splt
-}


