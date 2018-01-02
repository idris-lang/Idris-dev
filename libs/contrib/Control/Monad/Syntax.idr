module Control.Monad.Syntax

%default total
%access public export

infixr 1 =<<, <=<, >=>

||| Left-to-right Kleisli composition of monads.
(>=>) : Monad m => (a -> m b) -> (b -> m c) -> (a -> m c)
(>=>) f g = \x => f x >>= g

||| Right-to-left Kleisli composition of monads, flipped version of `>=>`.
(<=<) : Monad m => (b -> m c) -> (a -> m b) -> (a -> m c)
(<=<) = flip (>=>)

||| Right-to-left monadic bind, flipped version of `>>=`.
(=<<) : Monad m => (a -> m b) -> m a -> m b
(=<<) = flip (>>=)
