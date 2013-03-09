module Category.Arrow

import Data.Morphisms
import Control.Category

%access public

infixr 3 ***
infixr 3 &&&

class Category arr => Arrow (arr : Type -> Type -> Type) where
  arrow  : (a -> b) -> arr a b
  first  : arr a b -> arr (a, c) (b, c)
  second : arr a b -> arr (c, a) (c, b)
  (***)  : arr a b -> arr a' b' -> arr (a, a') (b, b')
  (&&&)  : arr a b -> arr a b' -> arr a (b, b')

instance Arrow Morphism where
  arrow  f            = Mor f
  first  (Mor f)      = Mor $ \(a, b) => (f a, b)
  second (Mor f)      = Mor $ \(a, b) => (a, f b)
  (Mor f) *** (Mor g) = Mor $ \(a, b) => (f a, g b)
  (Mor f) &&& (Mor g) = Mor $ \a => (f a, g a)

instance Monad m => Arrow (Kleislimorphism m) where
  arrow f = Kleisli (return . f)
  first (Kleisli f) =  Kleisli $ \(a, b) => do x <- f a
                                               return (x, b)

  second (Kleisli f) = Kleisli $ \(a, b) => do x <- f b
                                               return (a, x)

  (Kleisli f) *** (Kleisli g) = Kleisli $ \(a, b) => do x <- f a
                                                        y <- g b
                                                        return (x, y)

  (Kleisli f) &&& (Kleisli g) = Kleisli $ \a => do x <- f a
                                                   y <- g a
                                                   return (x, y)

