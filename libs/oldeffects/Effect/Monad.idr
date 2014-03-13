module Effect.Monad

import Effects

-- Eff is a monad too, so we can happily use it in a monad transformer.

using (xs : List EFFECT, m : Type -> Type)
  instance Functor (EffM m xs xs) where
    map f prog = do t <- prog
                    value (f t)

  instance Applicative (EffM m xs xs) where
    pure = value
    (<$>) f a = do f' <- f
                   a' <- a
                   value (f' a')

  instance Monad (EffM m xs xs) where
    (>>=) = ebind


