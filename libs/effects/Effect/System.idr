module Effect.System

-- Various system interaction features (this is not necessarily the right way
-- to split them up, I just need some of them now :))

import Effects
import System
import Control.IOExcept

%access public export

data System : Effect where
     Args : sig System (List String)
     Time : sig System Integer
     GetEnv : String -> sig System (Maybe String)
     CSystem : String -> sig System Int

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

getArgs : Eff (List String) [SYSTEM]
getArgs = call Args

time : Eff Integer [SYSTEM]
time = call Time

getEnv : String -> Eff (Maybe String) [SYSTEM]
getEnv s = call $ GetEnv s

system : String -> Eff Int [SYSTEM]
system s = call $ CSystem s
