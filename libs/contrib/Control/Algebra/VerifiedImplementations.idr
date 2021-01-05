module Control.VerifiedInterfaces

import Interfaces.Verified
import Control.Algebra
import Control.Algebra.CyclicGroup
import Control.Algebra.Lattice
import Control.Algebra.NumericImplementations
import Data.Vect
import Data.ZZ
import Data.Sign
import Data.Bool.Extra
import Data.Morphisms
import Control.Monad.Identity

%default total
%access public export

-- Due to these being basically unused and difficult to implement,
-- they're in contrib for a bit. Once a design is found that lets them
-- be implemented for a number of implementations, and we get those
-- implementations, then some of them can move back to base (or even
-- prelude, in the cases of Functor, Applicative, Monad, Semigroup,
-- and Monoid).

-- Functor

functorIdentity' : VerifiedFunctor f => (x : f a) -> map Basics.id x = x
functorIdentity' {f} = functorIdentity {f} id (\x => Refl)

VerifiedFunctor (Pair a) where
  functorIdentity g p (a,b) = rewrite p b in Refl
  functorComposition (a,b) g1 g2 = Refl

VerifiedFunctor (Either a) where
  functorIdentity _ _ (Left _) = Refl
  functorIdentity _ p (Right x) = cong (p x)
  functorComposition (Left _) _ _ = Refl
  functorComposition (Right _) _ _ = Refl

VerifiedFunctor Maybe where
  functorIdentity _ _ Nothing = Refl
  functorIdentity g p (Just x) = rewrite p x in Refl
  functorComposition Nothing g1 g2 = Refl
  functorComposition (Just x) g1 g2 = Refl

VerifiedFunctor List where
  functorIdentity _ _ [] = Refl
  functorIdentity g p (x :: xs) = rewrite p x in cong (functorIdentity g p xs)
  functorComposition [] _ _ = Refl
  functorComposition (x :: xs) f g = rewrite functorComposition xs f g in Refl

VerifiedFunctor (Vect n) where
  functorIdentity _ _ [] = Refl
  functorIdentity g p (x :: xs) = rewrite p x in cong (functorIdentity g p xs)
  functorComposition [] _ _ = Refl
  functorComposition (x :: xs) f g = rewrite functorComposition xs f g in Refl

-- Applicative

VerifiedApplicative (Either a) where
  applicativeMap (Left x) g = Refl
  applicativeMap (Right x) g = Refl
  applicativeIdentity (Left x) = Refl
  applicativeIdentity (Right x) = Refl
  applicativeComposition (Left x) (Left y) (Left z) = Refl
  applicativeComposition (Left x) (Left y) (Right z) = Refl
  applicativeComposition (Left x) (Right y) (Left z) = Refl
  applicativeComposition (Left x) (Right y) (Right z) = Refl
  applicativeComposition (Right x) (Left y) (Left z) = Refl
  applicativeComposition (Right x) (Left y) (Right z) = Refl
  applicativeComposition (Right x) (Right y) (Left z) = Refl
  applicativeComposition (Right x) (Right y) (Right z) = Refl
  applicativeHomomorphism x g = Refl
  applicativeInterchange x (Left y) = Refl
  applicativeInterchange x (Right y) = Refl

private
foldrConcatEq : (g1 : List (a -> b)) -> (g2 : List (a -> b)) ->
                (xs : List a) ->
                foldr (\f, meth => map f xs ++ meth) [] (g1 ++ g2) = foldr (\f, meth => map f xs ++ meth) [] g1 ++ foldr (\f, meth => map f xs ++ meth) [] g2
foldrConcatEq [] _ _ = Refl
foldrConcatEq (g1 :: gs1) gs2 xs =
  trans
    (cong $ foldrConcatEq gs1 gs2 xs)
    (appendAssociative
      (map g1 xs)
      (foldr (\f, meth => map f xs ++ meth) [] gs1)
      (foldr (\f, meth => map f xs ++ meth) [] gs2))

private
foldrConcatEq' : (x1 : List a) -> (x2 : List a) ->
                 (g : a -> List b) ->
                 foldr (\x, meth => g x ++ meth) [] (x1 ++ x2) = foldr (\x, meth => g x ++ meth) [] x1 ++ foldr (\x, meth => g x ++ meth) [] x2
foldrConcatEq' [] _ _ = Refl
foldrConcatEq' (x1 :: xs1) xs2 g =
  trans
    (cong {f=((++) $ g x1)} $ foldrConcatEq' xs1 xs2 g)
    (appendAssociative
      (g x1)
      (foldr (\x, meth => g x ++ meth) [] xs1)
      (foldr (\x, meth => g x ++ meth) [] xs2))

private
foldrMapCombine : (xs : List a) -> (gs1 : List (a -> b)) -> (g2 : b -> c) ->
                  map g2 (foldr (\g, meth => map g xs ++ meth) [] gs1) =
                  foldr (\g, meth => map g xs ++ meth) [] (map ((.) g2) gs1)
foldrMapCombine xs [] g2 = Refl
foldrMapCombine xs (g1 :: gs1) g2 =
  trans
    (mapAppendDistributive g2 (map g1 xs) (foldr (\g, meth => map g xs ++ meth) [] gs1))
    (appendCong2 (sym $ functorComposition xs g1 g2) (foldrMapCombine xs gs1 g2))

VerifiedApplicative List where
  applicativeMap [] f = Refl
  applicativeMap (x :: xs) f = rewrite applicativeMap xs f in Refl
  applicativeIdentity xs = rewrite sym $ applicativeMap xs id in functorIdentity' xs
  applicativeComposition _ _ [] = Refl
  applicativeComposition xs gs1 (g2 :: gs2) = trans
    (trans
      (foldrConcatEq (map ((.) g2) gs1) (foldr (\g, meth => map g gs1 ++ meth) [] (map (.) gs2 ++ [])) xs)
      (cong $ applicativeComposition xs gs1 gs2))
    (sym $
      cong {f=(++ foldr (\g, meth => map g (foldr (\g', meth' => map g' xs ++ meth') [] gs1) ++ meth) [] gs2)} $
        foldrMapCombine xs gs1 g2)
  applicativeHomomorphism x g = Refl
  applicativeInterchange x [] = Refl
  applicativeInterchange x (g :: gs) = cong $ applicativeInterchange x gs

VerifiedApplicative (Vect n) where
  applicativeMap [] f = Refl
  applicativeMap (x :: xs) f = rewrite applicativeMap xs f in Refl
  applicativeIdentity xs = rewrite sym $ applicativeMap xs id in functorIdentity' xs
  applicativeComposition [] [] [] = Refl
  applicativeComposition (x :: xs) (f :: fs) (g :: gs) = rewrite applicativeComposition xs fs gs in Refl
  applicativeHomomorphism = prf
    where prf : with Vect ((x : a) -> (f : a -> b) -> zipWith Basics.apply (replicate m f) (replicate m x) = replicate m (f x))
          prf {m = Z} x f = Refl
          prf {m = S k} x f = rewrite prf {m = k} x f in Refl
  applicativeInterchange = prf
    where prf : with Vect ((x : a) -> (f : Vect m (a -> b)) -> zipWith Basics.apply f (replicate m x) = zipWith Basics.apply (replicate m (\f' => f' x)) f)
          prf {m = Z} x [] = Refl
          prf {m = S k} x (f :: fs) = rewrite prf x fs in Refl

VerifiedApplicative Maybe where
  applicativeMap Nothing g = Refl
  applicativeMap (Just x) g = Refl
  applicativeIdentity Nothing = Refl
  applicativeIdentity (Just x) = Refl
  applicativeComposition Nothing Nothing Nothing = Refl
  applicativeComposition Nothing Nothing (Just x) = Refl
  applicativeComposition Nothing (Just x) Nothing = Refl
  applicativeComposition Nothing (Just x) (Just y) = Refl
  applicativeComposition (Just x) Nothing Nothing = Refl
  applicativeComposition (Just x) Nothing (Just y) = Refl
  applicativeComposition (Just x) (Just y) Nothing = Refl
  applicativeComposition (Just x) (Just y) (Just z) = Refl
  applicativeHomomorphism x g = Refl
  applicativeInterchange x Nothing = Refl
  applicativeInterchange x (Just y) = Refl

-- Monad

VerifiedMonad (Either a) where
  monadApplicative (Left x) (Left y) = Refl
  monadApplicative (Left x) (Right y) = Refl
  monadApplicative (Right x) (Left y) = Refl
  monadApplicative (Right x) (Right y) = Refl
  monadLeftIdentity x f = Refl
  monadRightIdentity (Left x) = Refl
  monadRightIdentity (Right x) = Refl
  monadAssociativity (Left x) f g = Refl
  monadAssociativity (Right x) f g = Refl

VerifiedMonad Maybe where
  monadApplicative Nothing Nothing = Refl
  monadApplicative Nothing (Just x) = Refl
  monadApplicative (Just x) Nothing = Refl
  monadApplicative (Just x) (Just y) = Refl
  monadLeftIdentity x f = Refl
  monadRightIdentity Nothing = Refl
  monadRightIdentity (Just x) = Refl
  monadAssociativity Nothing f g = Refl
  monadAssociativity (Just x) f g = Refl

VerifiedMonad List where
  monadApplicative [] _ = Refl
  monadApplicative (x :: xs) [] = Refl
  monadApplicative (g :: gs) xs = appendCong2 (mapFoldrEq g xs) (monadApplicative gs xs) where
    mapFoldrEq : (f : a -> b) -> (x : List a) -> map f x = foldr (\x1, meth => f x1 :: meth) [] x
    mapFoldrEq _ [] = Refl
    mapFoldrEq f (_ :: x) = cong $ mapFoldrEq f x
  monadLeftIdentity x f = appendNilRightNeutral (f x)
  monadRightIdentity [] = Refl
  monadRightIdentity (x :: xs) = cong $ monadRightIdentity xs
  monadAssociativity [] _ _ = Refl
  monadAssociativity (x :: xs) g1 g2 =
    trans
      (foldrConcatEq' (g1 x) (foldr (\x1, meth => g1 x1 ++ meth) [] xs) g2)
      (cong $ monadAssociativity xs g1 g2)

-- Alternative

VerifiedAlternative Maybe where
  alternativeLeftIdentity _ = Refl
  alternativeRightIdentity Nothing = Refl
  alternativeRightIdentity (Just _) = Refl
  alternativeAssociativity Nothing _ _ = Refl
  alternativeAssociativity (Just _) _ _ = Refl

VerifiedAlternative List where
  alternativeLeftIdentity _ = Refl
  alternativeRightIdentity = appendNilRightNeutral
  alternativeAssociativity = appendAssociative

-- Semigroup

implementation VerifiedSemigroup (List a) where
  semigroupOpIsAssociative = appendAssociative

[PlusNatSemiV] VerifiedSemigroup Nat using PlusNatSemi where
  semigroupOpIsAssociative = plusAssociative

[MultNatSemiV] VerifiedSemigroup Nat using MultNatSemi where
  semigroupOpIsAssociative = multAssociative

[PlusZZSemiV] VerifiedSemigroup ZZ using PlusZZSemi where
  semigroupOpIsAssociative = plusAssociativeZ

[MultZZSemiV] VerifiedSemigroup ZZ using MultZZSemi where
  semigroupOpIsAssociative = multAssociativeZ

-- Monoid

[PlusNatMonoidV] VerifiedMonoid Nat using PlusNatSemiV, PlusNatMonoid where
   monoidNeutralIsNeutralL = plusZeroRightNeutral
   monoidNeutralIsNeutralR = plusZeroLeftNeutral

[MultNatMonoidV] VerifiedMonoid Nat using MultNatSemiV, MultNatMonoid where
  monoidNeutralIsNeutralL = multOneRightNeutral
  monoidNeutralIsNeutralR = multOneLeftNeutral

[PlusZZMonoidV] VerifiedMonoid ZZ using PlusZZSemiV, PlusZZMonoid where
   monoidNeutralIsNeutralL = plusZeroRightNeutralZ
   monoidNeutralIsNeutralR = plusZeroLeftNeutralZ

[MultZZMonoidV] VerifiedMonoid ZZ using MultZZSemiV, MultZZMonoid where
  monoidNeutralIsNeutralL = multOneRightNeutralZ
  monoidNeutralIsNeutralR = multOneLeftNeutralZ

implementation VerifiedMonoid (List a) where
  monoidNeutralIsNeutralL = appendNilRightNeutral
  monoidNeutralIsNeutralR xs = Refl

-- Group

VerifiedGroup ZZ using PlusZZMonoidV where
  groupInverseIsInverseR k = rewrite sym $ multCommutativeZ (NegS 0) k in
                             rewrite multNegLeftZ 0 k in
                             rewrite multOneLeftNeutralZ k in
                             plusNegateInverseRZ k

-- Every integer can be gotten by repeatedly adding or subtracting 1.
CyclicGroup ZZ where
  generator = (1 ** \x => (x **
    case x of
      (Pos Z) => Refl
      (Pos (S k)) => mtimesSuccPos k
      (NegS k) => mtimesSuccNeg k))
    where
    mtimesSuccPos : (k : Nat) -> Pos (S k) = 1 + (mtimes' k 1)
    mtimesSuccPos Z = Refl
    mtimesSuccPos (S k) = rewrite sym $ mtimesSuccPos k in Refl

    mtimesSuccNeg : (k : Nat) -> NegS k = -1 + mtimes' k (-1)
    mtimesSuccNeg Z = Refl
    mtimesSuccNeg (S k) = rewrite sym $ mtimesSuccNeg k in Refl

-- Ring

VerifiedRing ZZ where
  ringOpIsAssociative = multAssociativeZ
  ringOpIsDistributiveL = multDistributesOverPlusRightZ
  ringOpIsDistributiveR = multDistributesOverPlusLeftZ

VerifiedRingWithUnity ZZ where
  ringWithUnityIsUnityL = multOneRightNeutralZ
  ringWithUnityIsUnityR = multOneLeftNeutralZ

-- Lattice

VerifiedJoinSemilattice Nat where
  joinSemilatticeJoinIsAssociative = maximumAssociative
  joinSemilatticeJoinIsCommutative = maximumCommutative
  joinSemilatticeJoinIsIdempotent  = maximumIdempotent

VerifiedJoinSemilattice Bool where
  joinSemilatticeJoinIsAssociative = orAssociative
  joinSemilatticeJoinIsCommutative = orCommutative
  joinSemilatticeJoinIsIdempotent = orSameNeutral


VerifiedMeetSemilattice Nat where
  meetSemilatticeMeetIsAssociative = minimumAssociative
  meetSemilatticeMeetIsCommutative = minimumCommutative
  meetSemilatticeMeetIsIdempotent  = minimumIdempotent

VerifiedMeetSemilattice Bool where
  meetSemilatticeMeetIsAssociative = andAssociative
  meetSemilatticeMeetIsCommutative = andCommutative
  meetSemilatticeMeetIsIdempotent = andSameNeutral

VerifiedBoundedJoinSemilattice Nat where
  joinBottomIsIdentity = maximumZeroNLeft

VerifiedBoundedJoinSemilattice Bool where
  joinBottomIsIdentity = orFalseNeutral

VerifiedBoundedMeetSemilattice Bool where
  meetTopIsIdentity = andTrueNeutral

----------------------------------------

VerifiedSemigroup a => VerifiedSemigroup (Identity a) where
  semigroupOpIsAssociative (Id l) (Id c) (Id r) =
    rewrite semigroupOpIsAssociative l c r in Refl

VerifiedMonoid a => VerifiedMonoid (Identity a) where
  monoidNeutralIsNeutralL (Id l) =
    rewrite monoidNeutralIsNeutralL l in Refl
  monoidNeutralIsNeutralR (Id r) =
    rewrite monoidNeutralIsNeutralR r in Refl

VerifiedSemigroup (Endomorphism a) where
  semigroupOpIsAssociative (Endo _) (Endo _) (Endo _) = Refl

VerifiedMonoid (Endomorphism a) where
  monoidNeutralIsNeutralL (Endo _) = Refl
  monoidNeutralIsNeutralR (Endo _) = Refl

VerifiedSemigroup Sign where
  semigroupOpIsAssociative Zero _ _ = Refl
  semigroupOpIsAssociative Plus Zero _ = Refl
  semigroupOpIsAssociative Minus Zero _ = Refl
  semigroupOpIsAssociative Plus Plus Zero = Refl
  semigroupOpIsAssociative Plus Minus Zero = Refl
  semigroupOpIsAssociative Minus Plus Zero = Refl
  semigroupOpIsAssociative Minus Minus Zero = Refl
  semigroupOpIsAssociative Plus Plus Plus = Refl
  semigroupOpIsAssociative Plus Minus Plus = Refl
  semigroupOpIsAssociative Minus Plus Plus = Refl
  semigroupOpIsAssociative Minus Minus Plus = Refl
  semigroupOpIsAssociative Plus Plus Minus = Refl
  semigroupOpIsAssociative Plus Minus Minus = Refl
  semigroupOpIsAssociative Minus Plus Minus = Refl
  semigroupOpIsAssociative Minus Minus Minus = Refl

VerifiedMonoid Sign where
  monoidNeutralIsNeutralL Plus = Refl
  monoidNeutralIsNeutralL Zero = Refl
  monoidNeutralIsNeutralL Minus = Refl

  monoidNeutralIsNeutralR Plus = Refl
  monoidNeutralIsNeutralR Zero = Refl
  monoidNeutralIsNeutralR Minus = Refl
