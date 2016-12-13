module Effect.Exception

import Effects
import System
import Control.IOExcept

%access public export

data Exception : Type -> Effect where
     Raise : a -> sig (Exception a) b

implementation Handler (Exception a) Maybe where
     handle _ (Raise e) k = Nothing

implementation Handler (Exception a) List where
     handle _ (Raise e) k = []

implementation Show a => Handler (Exception a) IO where
     handle _ (Raise e) k = do printLn e
                               (exit 1)

implementation Handler (Exception a) (IOExcept a) where
     handle _ (Raise e) k = ioe_fail e

implementation Handler (Exception a) (Either a) where
     handle _ (Raise e) k = Left e

EXCEPTION : Type -> EFFECT
EXCEPTION t = MkEff () (Exception t)

raise : a -> Eff b [EXCEPTION a]
raise err = call $ Raise err
