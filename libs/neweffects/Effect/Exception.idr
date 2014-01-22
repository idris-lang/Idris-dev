module Effect.Exception

import Effects
import System
import Control.IOExcept

data Exception : Type -> Effect where 
     Raise : a -> { () } Exception a b

instance Handler (Exception a) Maybe where
     handle _ (Raise e) k = Nothing

instance Show a => Handler (Exception a) IO where
     handle _ (Raise e) k = do print e
                               believe_me (exit 1)

instance Handler (Exception a) (IOExcept a) where
     handle _ (Raise e) k = ioM (return (Left e))

instance Handler (Exception a) (Either a) where
     handle _ (Raise e) k = Left e

EXCEPTION : Type -> EFFECT
EXCEPTION t = MkEff () (Exception t)

raise : a -> { [EXCEPTION a ] } Eff m b 
raise err = Raise err






-- TODO: Catching exceptions mid program?
-- probably need to invoke a new interpreter

-- possibly add a 'handle' to the Eff language so that an alternative
-- handler can be introduced mid interpretation?

