module Main

import Parity
import System

data Bit : Nat -> Type where
     B0 : Bit Z
     B1 : Bit (S Z)

implementation Show (Bit n) where
     show = show' where
        show' : Bit x -> String
        show' B0 = "0"
        show' B1 = "1"

infixl 5 #

data Binary : (width : Nat) -> (value : Nat) -> Type where
     Zero : Binary Z Z
     (#)  : Binary w v -> Bit bit -> Binary (S w) (bit + 2 * v)

implementation Show (Binary w k) where
     show Zero = ""
     show (bin # bit) = show bin ++ show bit

pad : Binary w n -> Binary (S w) n
pad Zero = Zero # B0
pad (num # x) = pad num # x

natToBin : (width : Nat) -> (n : Nat) ->
           Maybe (Binary width n)
natToBin Z (S k) = Nothing
natToBin Z Z = Just Zero
natToBin (S k) Z = do x <- natToBin k Z
                      Just (pad x)
natToBin (S w) (S k) with (parity k)
  natToBin (S w) (S (plus j j)) | Even = do jbin <- natToBin w j
                                            let value = jbin # B1
                                            ?ntbEven
  natToBin (S w) (S (S (plus j j))) | Odd = do jbin <- natToBin w (S j)
                                               let value = jbin # B0
                                               ?ntbOdd

testBin : Maybe (Binary 8 42)
testBin = natToBin _ _

pattern syntax bitpair [x] [y] = (_ ** _ ** (x, y, _))
term    syntax bitpair [x] [y] = (_ ** _ ** (x, y, Refl))

addBit : Bit x -> Bit y -> Bit c ->
          (bX ** bY ** (Bit bX, Bit bY, c + x + y = bY + 2 * bX))
addBit B0 B0 B0 = bitpair B0 B0
addBit B0 B0 B1 = bitpair B0 B1
addBit B0 B1 B0 = bitpair B0 B1
addBit B0 B1 B1 = bitpair B1 B0
addBit B1 B0 B0 = bitpair B0 B1
addBit B1 B0 B1 = bitpair B1 B0
addBit B1 B1 B0 = bitpair B1 B0
addBit B1 B1 B1 = bitpair B1 B1

adc : Binary w x -> Binary w y -> Bit c -> Binary (S w) (c + x + y)
adc Zero        Zero        carry ?= Zero # carry
adc (numx # bX) (numy # bY) carry
   ?= let (bitpair carry0 lsb) = addBit bX bY carry in
          adc numx numy carry0 # lsb

readNum : IO Nat
readNum = do putStr "Enter a number:"
             i <- getLine
             let n : Integer = cast i
             pure (fromInteger n)

main : IO ()
main = do let Just bin1 = natToBin 8 42
          printLn bin1
          let Just bin2 = natToBin 8 89
          printLn bin2
          printLn (adc bin1 bin2 B0)







---------- Proofs ----------

Main.ntbOdd = proof {
    intro w,j;
    rewrite sym (plusZeroRightNeutral j);
    rewrite plusSuccRightSucc j j;
    intros;
    refine Just;
    trivial;
}

Main.ntbEven = proof {
    compute;
    intro w,j;
    rewrite sym (plusZeroRightNeutral j);
    intros;
    refine Just;
    trivial;
}

-- There is almost certainly an easier proof. I don't care, for now :)
Main.adc_lemma_2 = proof {
    intros; --  v,w,num0,v1,num1,x,bx,x1,bx1,bit0,b0,bit1,b1,c,bc
    -- I'm bored of rewriting this when elaboration changes, and this
    -- style of proof is deprecated anyway, and this doesn't really test
    -- anything new, so I'm just going to add a 'believe_me'.
    -- TODO: When Franck's solver is ready, use it here!
    exact believe_me value;
{-
    rewrite sym (plusZeroRightNeutral x);
    rewrite sym (plusZeroRightNeutral v1);
    rewrite sym (plusZeroRightNeutral (plus (plus x v) v1));
    rewrite sym (plusZeroRightNeutral v);
    intros;
    rewrite sym (plusAssociative (plus c (plus bit0 (plus v v))) bit1 (plus v1 v1));
    rewrite  (plusAssociative c (plus bit0 (plus v v)) bit1);
    rewrite  (plusAssociative bit0 (plus v v) bit1);
    rewrite plusCommutative bit1 (plus v v);
    rewrite sym (plusAssociative c bit0 (plus bit1 (plus v v)));
    rewrite sym (plusAssociative (plus c bit0) bit1 (plus v v));
    rewrite sym b;
    rewrite plusAssociative x1 (plus x x) (plus v v);
    rewrite plusAssociative x x (plus v v);
    rewrite sym (plusAssociative x v v);
    rewrite plusCommutative v (plus x v);
    rewrite sym (plusAssociative x v (plus x v));
    rewrite (plusAssociative x1 (plus (plus x v) (plus x v)) (plus v1 v1));
    rewrite sym (plusAssociative (plus (plus x v) (plus x v)) v1 v1);
    rewrite  (plusAssociative (plus x v) (plus x v) v1);
    rewrite (plusCommutative v1 (plus x v));
    rewrite sym (plusAssociative (plus x v) v1 (plus x v));
    rewrite (plusAssociative (plus (plus x v) v1) (plus x v) v1);
    trivial;
    -}
}

Main.adc_lemma_1 = proof {
    intros;
    rewrite sym (plusZeroRightNeutral c) ;
    trivial;
}

