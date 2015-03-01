module Data.Erased

%access public
%default total

||| The erasure monad.
|||
||| Used when explicit modelling of erasure in the type system is needed.
data Erased : Type -> Type where

    ||| Construct an erased value from any value.
    Erase : .(x : a) -> Erased a

instance Functor Erased where
  f <$> (Erase x) = Erase (f x)

instance Applicative Erased where
  pure = Erase
  (<*>) (Erase f) (Erase x) = Erase (f x)

instance Monad Erased where
  (>>=) (Erase x) f = f x

||| Project the erased value out of the monad.
|||
||| This is usable only in types and other erased contexts,
||| where it won't cause erasure violations.
unerase : Erased a -> a
unerase (Erase x) = x
