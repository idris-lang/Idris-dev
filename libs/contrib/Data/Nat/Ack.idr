||| Properties of the Ackermann function.
module Data.Nat.Ackermann

%access public export

%default total

-- Primitive recursive functions are functions that can be calculated
-- by programs that don't use unbounded loops. Almost all common
-- mathematical functions are primitive recursive.

-- Uncomputable functions are functions that can't be calculated by
-- any programs at all. One example is the Busy Beaver function:
--   BB(k) = the maximum number of steps that can be executed by a
--           halting Turing machine with k states.
-- The values of the Busy Beaver function are unimaginably large for
-- any but the smallest inputs.

-- The Ackermann function is the most well-known example of a total
-- computable function that is not primitive recursive, i.e. a general
-- recursive function. It grows strictly faster than any primitive
-- recursive function, but also strictly slower than a function like
-- the Busy Beaver.

-- There are many variations of the Ackermann function. Here is one
-- common definition
-- (see https://sites.google.com/site/pointlesslargenumberstuff/home/2/ackermann)
-- that uses nested recursion:

ackRec : Nat -> Nat -> Nat
-- Base rule
ackRec Z m = S m
-- Prime rule
ackRec (S k) Z = ackRec k 1
-- Catastrophic rule
ackRec (S k) (S j) = ackRec k $ ackRec (S k) j

-- The so-called "base rule" and "prime rule" work together to ensure
-- termination. Happily, the Idris totality checker has no issues.

-- An unusual "repeating" defintion of the function is given in the
-- book The Little Typer:

ackRep : Nat -> Nat -> Nat
ackRep Z = (+) 1
ackRep (S k) = repeat (ackRep k)
  where
    repeat : (Nat -> Nat) -> Nat -> Nat
    repeat f Z = f 1
    repeat f (S k) = f (repeat f k)

-- These two definitions don't look like they define the same
-- function, but they do:

ackRepRec : (n, m : Nat) -> ackRep n m = ackRec n m
ackRepRec Z _ = Refl
ackRepRec (S k) Z = ackRepRec k 1
ackRepRec (S k) (S j) =
  rewrite sym $ ackRepRec (S k) j in
    ackRepRec k $ ackRep (S k) j
