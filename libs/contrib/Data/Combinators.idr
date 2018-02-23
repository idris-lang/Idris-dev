||| Combinators that are thought to be at least situationally useful, mostly for
||| tacit (or point-free) programming. "To Mock a Mockingbird" refers to the book
||| "To Mock a Mockingbird and Other Logic Puzzles: Including an Amazing Adventure
||| in Combinatory Logic", by Raymond Smullyan (which the author of this module
||| hasn't actually read). See
||| http://www.angelfire.com/tx4/cus/combinator/birds.html and
||| https://hackage.haskell.org/package/data-aviary-0.4.0/docs/Data-Aviary-Birds.html
||| an (incomplete?) list of birds introduced.

module Data.Combinators

%default total
%access public export

||| Psi combinator - psi bird (?) - Haskell on.
on : (b -> b -> c) -> (a -> b) -> (a -> a -> c)
on f g x y = g x `f` g y


infixl 9 ...
||| Blackbird, as named in "To Mock a Mockingbird". This is like
||| function composition, but second function takes two arguments. See the talk
||| "Point-Free or Die: Tacit Programming in Haskell and Beyond" by Amar Shah
||| (https://youtu.be/seVSlKazsNk).
(...) : (c -> d) -> (a -> b -> c) -> (a -> b -> d)
(...) = (.) . (.)

||| Warbler, as named in "To Mock a Mockingbird".
||| See http://code.jsoftware.com/wiki/Vocabulary/tilde
||| Equivalent to `join` on the Reader monad (`(->) e` in Haskell)
reflex : (a -> a -> b) -> (a -> b)
reflex f x = f x x

||| Phoenix, according to Data.Aviary.
||| See http://code.jsoftware.com/wiki/Vocabulary/fork.
||| Equivalent to `liftA2` on the Reader monad (`(->) e` in Haskell)
fork2 : (b -> c -> d) -> (a -> b) -> (a -> c) -> (a -> d)
fork2 f g h x = f (g x) (h x)
