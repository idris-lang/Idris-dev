import Control.Algebra

import Data.ZZ

%access public export
%default total

----------------------------------------

-- The Verified constraints here are required
-- to work around an interface resolution bug.

-- https://github.com/idris-lang/Idris-dev/issues/4853
-- https://github.com/idris-lang/Idris2/issues/72

mtimes' : VerifiedMonoid a => (n : Nat) -> a -> a
mtimes' Z x = neutral
mtimes' (S k) x = x <+> mtimes' k x

gtimes : VerifiedGroup a => (n : ZZ) -> a -> a
gtimes (Pos k) x = mtimes' k x
gtimes (NegS k) x = mtimes' (S k) (inverse x)

----------------------------------------

mtimesTimes : VerifiedMonoid a => (x : a) -> (n, m : Nat) ->
  mtimes' (n + m) x = mtimes' n x <+> mtimes' m x
mtimesTimes x Z m = sym $ monoidNeutralIsNeutralR $ mtimes' m x
mtimesTimes x (S k) m =
  rewrite mtimesTimes x k m in
    semigroupOpIsAssociative x (mtimes' k x) (mtimes' m x)

-- TODO: prove this. It's definitely true in spirit, and I'm pretty
-- sure the implementation of gtimes is correct, but working with ZZ
-- is not easy.
postulate
gtimesTimes : VerifiedGroup a => (x : a) -> (n, m : ZZ) ->
  gtimes (n + m) x = gtimes n x <+> gtimes m x

gtimesCommutes : VerifiedGroup a => (x : a) -> (n, m : ZZ) ->
  gtimes n x <+> gtimes m x = gtimes m x <+> gtimes n x
gtimesCommutes x n m =
  rewrite sym $ gtimesTimes x n m in
    rewrite plusCommutativeZ n m in
      gtimesTimes x m n

||| A cyclic group is a group in which every element can be gotten by
||| repeatedly adding or subtracting a particular element known as the
||| generator.
interface VerifiedGroup a => CyclicGroup a where
  generator : (g : a ** (x : a) -> (n : ZZ ** x = gtimes n g))

||| Every cyclic group is commutative.
CyclicGroup a => AbelianGroup a where
  abelianGroupOpIsCommutative {a} l r =
    let
      (g ** gen) = generator {a=a}
      (n ** gl) = gen l
      (m ** gr) = gen r
        in
    rewrite gl in
      rewrite gr in
        gtimesCommutes g n m
