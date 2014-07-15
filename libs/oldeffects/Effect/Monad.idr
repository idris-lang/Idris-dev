module Effect.Monad

import Effects

-- Eff is a monad too, so we can happily use it in a monad transformer.

using (xs : List EFFECT, m : Type -> Type)
  instance Functor (\a => EffM m a xs (\v => xs)) where
    map f prog = do t <- prog
                    value (f t)

  instance Applicative (\a => EffM m a xs (\v => xs)) where
    pure = value
    (<$>) f a = do f' <- f
                   a' <- a
                   value (f' a')

  instance Monad (\a => Eff m a xs (\v => xs)) where
    (>>=) = Effects.(>>=)


