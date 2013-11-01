module reg022

data Result str a = Success str a | Failure String

instance Functor (Result str) where
   map f (Success s x) = Success s (f x)
   map f (Failure e  ) = Failure e

ParserT : (Type -> Type) -> Type -> Type -> Type
ParserT m str a = str -> m (Result str a)

ap : Monad m => ParserT m str (a -> b) -> ParserT m str a ->
                ParserT m str b
ap f x = \s => do f' <- f s
                  case f' of
                          Failure e => (pure (Failure e))
                          Success s' g => x s' >>= pure . map g

