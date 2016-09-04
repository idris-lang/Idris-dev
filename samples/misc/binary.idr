module main

data Bit : Nat -> Type where
     b0 : Bit 0
     b1 : Bit 1

implementation Show (Bit n) where
     show b0 = "0"
     show b1 = "1"

infixl 5 #

data Binary : (width : Nat) -> (value : Nat) -> Type where
     zero : Binary Z Z
     (#)  : Binary w v -> Bit bit -> Binary (S w) (bit + 2 * v)

implementation Show (Binary w k) where
     show zero = ""
     show (bin # bit) = show bin ++ show bit

pattern syntax bitpair [x] [y] = (_ ** (_ ** (x, y, _)))
term    syntax bitpair [x] [y] = (_ ** (_ ** (x, y, Refl)))

addBit : Bit x -> Bit y -> Bit c ->
          (bx ** (by ** (Bit bx, Bit by, c + x + y = by + 2 * bx)))
addBit b0 b0 b0 = bitpair b0 b0
addBit b0 b0 b1 = bitpair b0 b1
addBit b0 b1 b0 = bitpair b0 b1
addBit b0 b1 b1 = bitpair b1 b0
addBit b1 b0 b0 = bitpair b0 b1
addBit b1 b0 b1 = bitpair b1 b0
addBit b1 b1 b0 = bitpair b1 b0
addBit b1 b1 b1 = bitpair b1 b1

adc : Binary w x -> Binary w y -> Bit c -> Binary (S w) (c + x + y)
adc zero        zero        carry ?= zero # carry
adc (numx # bx) (numy # by) carry
   ?= let (bitpair carry0 lsb) = addBit bx by carry in
          adc numx numy carry0 # lsb

main : IO ()
main = do let n1 = zero # b1 # b0 # b1 # b0
          let n2 = zero # b1 # b1 # b1 # b0
          print (adc n1 n2 b0)









---------- Proofs ----------

-- There is almost certainly an easier proof. I don't care, for now :)

main.adc_lemma_2 = proof {
    intro c,w,v,bit0,num0;
    intro b0,v1,bit1,num1,b1;
    intro bc,x,x1,bx,bx1,prf;
    intro;
    rewrite sym (plusZeroRightNeutral v);
    rewrite sym (plusZeroRightNeutral v1);
    rewrite sym (plusAssociative (plus c (plus bit0 (plus v v))) bit1 (plus v1 v1));
    rewrite (plusAssociative c (plus bit0 (plus v v)) bit1);
    rewrite (plusAssociative bit0 (plus v v) bit1);
    rewrite sym (plusCommutative (plus v v) bit1);
    rewrite sym (plusAssociative c bit0 (plus bit1 (plus v v)));
    rewrite sym (plusAssociative (plus c bit0) bit1 (plus v v));
    rewrite sym prf;
    rewrite sym (plusZeroRightNeutral x);
    rewrite plusAssociative x1 (plus x x) (plus v v);
    rewrite plusAssociative x x (plus v v);
    rewrite sym (plusAssociative x v v);
    rewrite plusCommutative v (plus x v);
    rewrite sym (plusAssociative x v (plus x v));
    rewrite plusAssociative x1 (plus (plus x v) (plus x v)) (plus v1 v1);
    rewrite plusAssociative (plus x v) (plus x v) (plus v1 v1);
    rewrite plusAssociative x v (plus v1 v1);
    rewrite sym (plusAssociative v v1 v1);
    rewrite sym (plusAssociative x (plus v v1) v1);
    rewrite sym (plusAssociative x v v1);
    rewrite sym (plusCommutative (plus (plus x v) v1) v1);
    rewrite plusZeroRightNeutral (plus (plus x v) v1);
    rewrite sym (plusAssociative (plus x v) v1 (plus (plus (plus x v) v1) Z));
    trivial;
}

main.adc_lemma_1 = proof {
    intros;
    rewrite sym (plusZeroRightNeutral c) ;
    trivial;
}
