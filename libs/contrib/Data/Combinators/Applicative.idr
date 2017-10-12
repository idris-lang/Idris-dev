||| Enable applicative-style syntax (Mostly f <$> g <*> h and idiom brackets)
||| for function composition:
module Data.Combinators.Applicative

import Data.Combinators

%default total
%access public export

||| Pure is just const, also known as the K combinator
pure : a -> b -> a
pure = const

||| `map` is (.), but isn't here to discourage that use of the syntax.
||| `foo <$> bar <*> baz` applies `foo` to the results of `bar` and `baz`,
||| and generalizes to multiple arguments.
(<$>) : (b -> c) -> (a -> b) -> (a -> c)
(<$>) f g x = f (g x)

||| Starling, as named in "To Mock a Mockingbird". This is the S combinator.
||| Equivalent to `<*>` on the Reader monad (`(->) e` in Haskell).
||| See http://code.jsoftware.com/wiki/Vocabulary/hook.
(<*>) : (a -> b -> c) -> (a -> b)-> (a -> c)
(<*>) f g x = f x (g x)

liftA2 : (b -> c -> d) -> (a -> b) -> (a -> c) -> (a -> d)
liftA2 = fork2
