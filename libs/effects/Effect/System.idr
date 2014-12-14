module Effect.System

-- Various system interaction features (this is not necessarily the right way
-- to split them up, I just need some of them now :))

import Effects
import public System
import Control.IOExcept

data System : Effect where
     Args : { () } System (List String)
     Time : { () } System Int
     GetEnv : String -> { () } System (Maybe String)
     CSystem : String -> { () } System Int

instance Handler System IO where
    handle () Args k = do x <- getArgs; k x ()
    handle () Time k = do x <- time; k x ()
    handle () (GetEnv s) k = do x <- getEnv s; k x ()
    handle () (CSystem s) k = do x <- system s; k x ()

instance Handler System (IOExcept a) where
    handle () Args k = do x <- ioe_lift getArgs; k x ()
    handle () Time k = do x <- ioe_lift time; k x ()
    handle () (GetEnv s) k = do x <- ioe_lift $ getEnv s; k x ()
    handle () (CSystem s) k = do x <- ioe_lift $ system s; k x ()

--- The Effect and associated functions

SYSTEM : EFFECT
SYSTEM = MkEff () System

getArgs : { [SYSTEM] } Eff (List String)
getArgs = call Args

time : { [SYSTEM] } Eff Int
time = call Time

getEnv : String -> { [SYSTEM] } Eff (Maybe String)
getEnv s = call $ GetEnv s

system : String -> { [SYSTEM] } Eff Int
system s = call $ CSystem s
