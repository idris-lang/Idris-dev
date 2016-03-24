module Effect.Trans

import Effects

%access public export

data Trans : (Type -> Type) -> Effect where
  Lift : m a -> sig (Trans m) a

-- using (m : Type -> Type)
implementation Monad m => Handler (Trans m) m where
     handle st (Lift op) k = do x <- op
                                k x ()

TRANS : (Type -> Type) -> EFFECT
TRANS m = MkEff () (Trans m)

lift : m a -> Eff a [TRANS m]
lift op = call $ Lift op

