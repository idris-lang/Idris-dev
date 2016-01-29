module Effect.Monad

import Effects

%access public export

data MonadEffT : List EFFECT -> (Type -> Type) -> Type -> Type where
     MkMonadEffT : EffM m a xs (\v => xs) -> MonadEffT xs m a

implementation Functor (MonadEffT xs f) where
    map f (MkMonadEffT x) = MkMonadEffT (do x' <- x
                                            pure (f x'))

implementation Applicative (MonadEffT xs f) where
    pure x = MkMonadEffT (pure x)
    (<*>) (MkMonadEffT f) (MkMonadEffT x) 
          = MkMonadEffT (do f' <- f
                            x' <- x
                            pure (f' x'))

implementation Monad (MonadEffT xs f) where
    (>>=) (MkMonadEffT x) f = MkMonadEffT (do x' <- x
                                              let MkMonadEffT fx = f x'
                                              fx)

implicit monadEffT : EffM m a xs (\v => xs) -> MonadEffT xs m a
monadEffT = MkMonadEffT

MonadEff : List EFFECT -> Type -> Type
MonadEff xs = MonadEffT xs id
