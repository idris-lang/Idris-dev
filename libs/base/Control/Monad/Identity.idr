module Control.Monad.Identity

%access public export

public export record Identity (a : Type) where
  constructor Id
  runIdentity : a

Functor Identity where
    map fn (Id a) = Id (fn a)

Applicative Identity where
    pure x = Id x
    (Id f) <*> (Id g) = Id (f g)

Monad Identity where
    (Id x) >>= k = k x

Show a => Show (Identity a) where
  showPrec d (Id x) = showCon d "Id" $ showArg x

Eq a => Eq (Identity a) where
  (Id x) == (Id y) = x == y

Ord a => Ord (Identity a) where
  compare (Id x) (Id y) = compare x y

Enum a => Enum (Identity a) where
  toNat (Id x) = toNat x
  fromNat n = Id $ fromNat n
  pred (Id n) = Id $ pred n

(Semigroup a) => Semigroup (Identity a) where
  (<+>) x y = Id (runIdentity x <+> runIdentity y)

(Monoid a) => Monoid (Identity a) where
  neutral = Id (neutral)