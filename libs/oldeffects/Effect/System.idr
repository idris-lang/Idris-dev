module Effect.System

-- Various system interaction features (this is not necessarily the right way
-- to split them up, I just need some of them now :))

import Effects
import System
import Control.IOExcept

data System : Effect where
     Args : { () } System (List String)
     Time : { () } System Int
     GetEnv : String -> { () } System (Maybe String)
     CSystem : String -> { () } System Int

implementation Handler System IO where
    handle () Args k = do x <- getArgs; k x ()
    handle () Time k = do x <- time; k x ()
    handle () (GetEnv s) k = do x <- getEnv s; k x ()
    handle () (CSystem s) k = do x <- system s; k x ()

implementation Handler System (IOExcept a) where
    handle () Args k = do x <- ioe_lift getArgs; k x ()
    handle () Time k = do x <- ioe_lift time; k x ()
    handle () (GetEnv s) k = do x <- ioe_lift $ getEnv s; k x ()
    handle () (CSystem s) k = do x <- ioe_lift $ system s; k x ()

--- The Effect and associated functions

SYSTEM : EFFECT
SYSTEM = MkEff () System

getArgs : Handler System e => { [SYSTEM] } Eff e (List String)
getArgs = call Args

time : Handler System e => { [SYSTEM] } Eff e Int
time = call Time

getEnv : Handler System e => String -> { [SYSTEM] } Eff e (Maybe String)
getEnv s = call $ GetEnv s

system : Handler System e => String -> { [SYSTEM] } Eff e Int
system s = call $ CSystem s
