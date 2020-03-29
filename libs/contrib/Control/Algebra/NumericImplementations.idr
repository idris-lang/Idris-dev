||| Implementations of algebraic interfaces (group, ring, etc) for numeric data types,
||| and Complex number types.
module Control.Algebra.NumericImplementations

import Control.Algebra
import Control.Algebra.Laws
import Control.Algebra.VectorSpace
import Data.Complex
import Data.ZZ

%access public export

-- Integer

Semigroup Integer where
  (<+>) = (+)

  semigroupOpIsAssociative = believe_me Integer

Monoid Integer where
  neutral = 0

  monoidNeutralIsNeutralL = believe_me Integer
  monoidNeutralIsNeutralR = believe_me Integer

Group Integer where
  inverse = (* -1)

  groupInverseIsInverseR = believe_me Integer

AbelianGroup Integer where
  abelianGroupOpIsCommutative = believe_me Integer

Ring Integer where
  (<.>) = (*)

  ringOpIsAssociative   = believe_me Integer
  ringOpIsDistributiveL = believe_me Integer
  ringOpIsDistributiveR = believe_me Integer

RingWithUnity Integer where
  unity = 1

  ringWithUnityIsUnityL = believe_me Integer
  ringWithUnityIsUnityR = believe_me Integer

-- Int

Semigroup Int where
  (<+>) = (+)

  semigroupOpIsAssociative = believe_me Int

Monoid Int where
  neutral = 0

  monoidNeutralIsNeutralL = believe_me Int
  monoidNeutralIsNeutralR = believe_me Int

Group Int where
  inverse = (* -1)

  groupInverseIsInverseR = believe_me Int

AbelianGroup Int where
  abelianGroupOpIsCommutative = believe_me Int

Ring Int where
  (<.>) = (*)

  ringOpIsAssociative   = believe_me Int
  ringOpIsDistributiveL = believe_me Int
  ringOpIsDistributiveR = believe_me Int

RingWithUnity Int where
  unity = 1

  ringWithUnityIsUnityL = believe_me Int
  ringWithUnityIsUnityR = believe_me Int

-- Double

Semigroup Double where
  (<+>) = (+)

  semigroupOpIsAssociative = believe_me Double

Monoid Double where
  neutral = 0

  monoidNeutralIsNeutralL = believe_me Double
  monoidNeutralIsNeutralR = believe_me Double

Group Double where
  inverse = (* -1)

  groupInverseIsInverseR = believe_me Double

AbelianGroup Double where
  abelianGroupOpIsCommutative = believe_me Double

Ring Double where
  (<.>) = (*)

  ringOpIsAssociative   = believe_me Double
  ringOpIsDistributiveL = believe_me Double
  ringOpIsDistributiveR = believe_me Double

RingWithUnity Double where
  unity = 1

  ringWithUnityIsUnityL = believe_me Double
  ringWithUnityIsUnityR = believe_me Double

CommutativeRing Double where
  ringOpIsCommutative = believe_me Double

Field Double where
  inverseM f _ = 1 / f

  fieldInverseIsInverseR = believe_me Double

-- Nat

[PlusNatSemi] Semigroup Nat where
  (<+>) = (+)
  semigroupOpIsAssociative = plusAssociative

[PlusNatMonoid] Monoid Nat using PlusNatSemi where
  neutral = 0
  monoidNeutralIsNeutralL = plusZeroRightNeutral
  monoidNeutralIsNeutralR = plusZeroLeftNeutral

[MultNatSemi] Semigroup Nat where
  (<+>) = (*)
  semigroupOpIsAssociative = multAssociative

[MultNatMonoid] Monoid Nat using MultNatSemi where
  neutral = 1
  monoidNeutralIsNeutralL = multOneRightNeutral
  monoidNeutralIsNeutralR = multOneLeftNeutral

-- ZZ

[PlusZZSemi] Semigroup ZZ where
  (<+>) = (+)
  semigroupOpIsAssociative = plusAssociativeZ

[PlusZZMonoid] Monoid ZZ using PlusZZSemi where
  neutral = 0
  monoidNeutralIsNeutralL = plusZeroRightNeutralZ
  monoidNeutralIsNeutralR = plusZeroLeftNeutralZ

Group ZZ using PlusZZMonoid where
  inverse = (* -1)

  groupInverseIsInverseR k =
    rewrite sym $ multCommutativeZ (NegS 0) k in
    rewrite multNegLeftZ 0 k in
    rewrite multOneLeftNeutralZ k in
    plusNegateInverseRZ k

AbelianGroup ZZ where
  abelianGroupOpIsCommutative = plusCommutativeZ

[MultZZSemi] Semigroup ZZ where
  (<+>) = (*)
  semigroupOpIsAssociative = multAssociativeZ

[MultZZMonoid] Monoid ZZ using MultZZSemi where
  neutral = 1
  monoidNeutralIsNeutralL = multOneRightNeutralZ
  monoidNeutralIsNeutralR = multOneLeftNeutralZ

Ring ZZ where
  (<.>) = (*)
  ringOpIsAssociative = multAssociativeZ
  ringOpIsDistributiveL = multDistributesOverPlusRightZ
  ringOpIsDistributiveR = multDistributesOverPlusLeftZ

RingWithUnity ZZ where
  unity = 1
  ringWithUnityIsUnityL = multOneRightNeutralZ
  ringWithUnityIsUnityR = multOneLeftNeutralZ

-- Complex

Semigroup a => Semigroup (Complex a) where
  (<+>) (a :+ b) (c :+ d) = (a <+> c) :+ (b <+> d)

  semigroupOpIsAssociative (a :+ x) (b :+ y) (c :+ z) =
    rewrite semigroupOpIsAssociative a b c in
      rewrite semigroupOpIsAssociative x y z in
        Refl

Monoid t => Monoid (Complex t) where
  neutral = (neutral :+ neutral)

  monoidNeutralIsNeutralL (a :+ x) =
    rewrite monoidNeutralIsNeutralL a in
      rewrite monoidNeutralIsNeutralL x in
        Refl

  monoidNeutralIsNeutralR (a :+ x) =
    rewrite monoidNeutralIsNeutralR a in
      rewrite monoidNeutralIsNeutralR x in
        Refl

Group t => Group (Complex t) where
  inverse (r :+ i) = (inverse r :+ inverse i)

  groupInverseIsInverseR (r :+ i) =
    rewrite groupInverseIsInverseR r in
      rewrite groupInverseIsInverseR i in
        Refl

AbelianGroup t => AbelianGroup (Complex t) where
  abelianGroupOpIsCommutative (a :+ i) (b :+ j) =
    rewrite abelianGroupOpIsCommutative a b in
      rewrite abelianGroupOpIsCommutative i j in
        Refl

-- A simple helper lemma
private abelianGroupRearrange : AbelianGroup t => (a, b, c, d : t) ->
  a <+> b <+> (c <+> d) = a <+> c <+> (b <+> d)
abelianGroupRearrange a b c d =
  rewrite sym $ semigroupOpIsAssociative a b (c <+> d) in
    rewrite semigroupOpIsAssociative b c d in
      rewrite abelianGroupOpIsCommutative b c in
    rewrite sym $ semigroupOpIsAssociative c b d in
  semigroupOpIsAssociative a c (b <+> d)

Ring t => Ring (Complex t) where
  (<.>) (a :+ b) (c :+ d) = (a <.> c <-> b <.> d) :+ (a <.> d <+> b <.> c)

  ringOpIsDistributiveR (a :+ x) (b :+ y) (c :+ z) =
    -- Distribute inverses (target z)
    rewrite sym $ multInverseInversesR (x <+> y) z in
      rewrite sym $ multInverseInversesR x z in
        rewrite sym $ multInverseInversesR y z in
    -- Shuffle terms
    rewrite shuffle a b c x y (inverse z) in
      rewrite shuffle a b z x y c in
        Refl where
    shuffle : (f, g, h, i, j, k : t) ->
      (f <+> g) <.> h <+> (i <+> j) <.> k =
        f <.> h <+> i <.> k <+> (g <.> h <+> j <.> k)
    shuffle f g h i j k =
      rewrite ringOpIsDistributiveR f g h in
        rewrite ringOpIsDistributiveR i j k in
      abelianGroupRearrange (f <.> h) (g <.> h) (i <.> k) (j <.> k)

  ringOpIsDistributiveL (a :+ x) (b :+ y) (c :+ z) =
    -- Distribute inverses (target x)
    rewrite sym $ multInverseInversesL x (y <+> z) in
      rewrite sym $ multInverseInversesL x y in
        rewrite sym $ multInverseInversesL x z in
    -- Shuffle terms
    rewrite shuffle a b c (inverse x) y z in
      rewrite shuffle a y z x b c in
        Refl where
    shuffle : (f, g, h, i, j, k : t) ->
      f <.> (g <+> h) <+> i <.> (j <+> k) =
        f <.> g <+> i <.> j <+> (f <.> h <+> i <.> k)
    shuffle f g h i j k =
      rewrite ringOpIsDistributiveL f g h in
        rewrite ringOpIsDistributiveL i j k in
      abelianGroupRearrange (f <.> g) (f <.> h) (i <.> j) (i <.> k)

  ringOpIsAssociative (a :+ x) (b :+ y) (c :+ z) =

    let
      b' = inverse b
      y' = inverse y
      bz = b <.> z
      yc = y <.> c
      xbz = x <.> bz
      xyc = x <.> yc
      ay = a <.> y
      ay' = a <.> y'
      xb = x <.> b
      ab = a <.> b
      xb' = x <.> b'
      xy' = x <.> y'
      bc = b <.> c
      y'z = y' <.> z
        in

    -- Distribute inverses (target y if possible, else b)
    rewrite ringOpIsDistributiveL x bz yc in
      rewrite inverseDistributesOverGroupOp xbz xyc in
        rewrite sym $ multInverseInversesR x yc in
          rewrite sym $ multInverseInversesL y c in
        rewrite sym $ multInverseInversesR x bz in
          rewrite sym $ multInverseInversesL b z in
        rewrite sym $ multInverseInversesL y z in
      rewrite sym $ multInverseInversesL (ay <+> xb) z in
        rewrite inverseDistributesOverGroupOp ay xb in
          rewrite sym $ multInverseInversesR a y in
            rewrite sym $ multInverseInversesR x b in
      rewrite sym $ multInverseInversesR x y in

    -- Distribute multiplications
    rewrite ringOpIsDistributiveR ab xy' z in
      rewrite ringOpIsDistributiveR ay xb c in
    rewrite ringOpIsDistributiveL a bz yc in
      rewrite ringOpIsDistributiveL x bc y'z in
    rewrite ringOpIsDistributiveL a bc y'z in
      rewrite ringOpIsDistributiveR ab xy' c in
        rewrite ringOpIsDistributiveR ay' xb' z in

    -- Shuffle the real part
    let
      abc = a <.> bc
      ay'z = a <.> y'z
      xb'z = x <.> (b' <.> z)
      xy'c = x <.> (y' <.> c)
        in
    rewrite shuffle abc ay'z xb'z xy'c in
      rewrite regroup a x b c y' c y' z b' z in

    -- Shuffle the imaginary part
    let
      abz = a <.> bz
      ayc = a <.> yc
      xbc = x <.> bc
      xy'z = x <.> y'z
        in
    rewrite shuffle abz ayc xbc xy'z in
      rewrite regroup a x b z y' z y c b c in

    Refl where

    shuffle : (p, q, r, s : t) ->
      p <+> q <+> (r <+> s) = p <+> s <+> (q <+> r)
    shuffle p q r s =
      rewrite sym $ semigroupOpIsAssociative p q (r <+> s) in
        rewrite abelianGroupOpIsCommutative r s in
          rewrite semigroupOpIsAssociative q s r in
          rewrite abelianGroupOpIsCommutative q s in
        rewrite sym $ semigroupOpIsAssociative s q r in
      semigroupOpIsAssociative p s (q <+> r)

    regroup : (aa, xx, x1, x2, x3, x4, x5, x6, x7, x8 : t) ->
      (aa <.> (x1 <.> x2) <+> xx <.> (x3 <.> x4) <+>
        (aa <.> (x5 <.> x6) <+> xx <.> (x7 <.> x8)))
      =
      (aa <.> x1 <.> x2 <+> xx <.> x3 <.> x4 <+>
        (aa <.> x5 <.> x6 <+> xx <.> x7 <.> x8))
    regroup aa xx x1 x2 x3 x4 x5 x6 x7 x8 =
      rewrite ringOpIsAssociative aa x1 x2 in
        rewrite ringOpIsAssociative aa x5 x6 in
      rewrite ringOpIsAssociative xx x3 x4 in
        rewrite ringOpIsAssociative xx x7 x8 in
      Refl

RingWithUnity t => RingWithUnity (Complex t) where
  unity = (unity :+ neutral)

  ringWithUnityIsUnityL {t} (a :+ x) =
    rewrite ringWithUnityIsUnityL a in
      rewrite ringWithUnityIsUnityL x in
    rewrite multNeutralAbsorbingR a in
      rewrite multNeutralAbsorbingR x in
    rewrite inverseNeutralIsNeutral {t=t} in
      rewrite monoidNeutralIsNeutralL a in
        rewrite monoidNeutralIsNeutralR x in
    Refl

  ringWithUnityIsUnityR (a :+ x) =
    rewrite ringWithUnityIsUnityR a in
      rewrite ringWithUnityIsUnityR x in
    rewrite multNeutralAbsorbingL a in
      rewrite multNeutralAbsorbingL x in
    rewrite inverseNeutralIsNeutral {t=t} in
      rewrite monoidNeutralIsNeutralL a in
        rewrite monoidNeutralIsNeutralL x in
    Refl

RingWithUnity a => Module a (Complex a) where
  (<#>) x = map (x <.>)

RingWithUnity a => InnerProductSpace a (Complex a) where
  (x :+ y) <||> z = realPart $ (x :+ inverse y) <.> z
