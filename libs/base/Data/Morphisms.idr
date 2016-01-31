module Data.Morphisms

%access public export

data Morphism : Type -> Type -> Type where
  Mor : (a -> b) -> Morphism a b

data Endomorphism : Type -> Type where
  Endo : (a -> a) -> Endomorphism a

data Kleislimorphism : (Type -> Type) -> Type -> Type -> Type where
  Kleisli : Monad m => (a -> m b) -> Kleislimorphism m a b

applyKleisli : Monad m => (Kleislimorphism m a b) -> a -> m b
applyKleisli (Kleisli f) a = f a

applyMor : Morphism a b -> a -> b
applyMor (Mor f) a = f a

applyEndo : Endomorphism a -> a -> a
applyEndo (Endo f) a = f a

implementation Functor (Morphism r) where
  map f (Mor a) = Mor (f . a)

implementation Applicative (Morphism r) where
  pure a                = Mor $ const a
  (Mor f) <*> (Mor a) = Mor $ \r => f r $ a r

implementation Monad (Morphism r) where
  (Mor h) >>= f = Mor $ \r => applyMor (f $ h r) r

implementation Semigroup (Endomorphism a) where
  (Endo f) <+> (Endo g) = Endo $ g . f

implementation Monoid (Endomorphism a) where
  neutral = Endo id

infixr 1 ~>

(~>) : Type -> Type -> Type
a ~> b = Morphism a b
