module Effect.Exception

import Effects
import System
import Control.IOExcept

data Exception : Type -> Effect where
     Raise : a -> sig (Exception a) b

instance Handler (Exception a) Maybe where
     handle _ (Raise e) k = Nothing

instance Handler (Exception a) List where
     handle _ (Raise e) k = []

instance Show a => Handler (Exception a) IO where
     handle _ (Raise e) k = do printLn e
                               believe_me (exit 1)

instance Handler (Exception a) (IOExcept a) where
     handle _ (Raise e) k = ioM (return (Left e))

instance Handler (Exception a) (Either a) where
     handle _ (Raise e) k = Left e

EXCEPTION : Type -> EFFECT
EXCEPTION t = MkEff () (Exception t)

raise : a -> Eff b [EXCEPTION a]
raise err = call $ Raise err
