module Effect.StdIO

import Effects
import Control.IOExcept

data StdIO : Effect where
     PutStr : String -> StdIO () () ()
     GetStr : StdIO () () String

instance Handler StdIO IO where
    handle () (PutStr s) k = do putStr s; k () ()
    handle () GetStr     k = do x <- getLine; k () x 

instance Handler StdIO (IOExcept a) where
    handle () (PutStr s) k = do ioe_lift (putStr s); k () ()
    handle () GetStr     k = do x <- ioe_lift getLine; k () x 

-- Handle effects in a pure way, for simulating IO for unit testing/proof

data IOStream a = MkStream (List String -> (a, List String))
  
injStream : a -> IOStream a
injStream v = MkStream (\x => (v, []))
  
instance Handler StdIO IOStream where
    handle () (PutStr s) k
       = MkStream (\x => case k () () of
                         MkStream f => let (res, str) = f x in
                                           (res, s :: str))
    handle {a} () GetStr k
       = MkStream (\x => case x of
                              [] => cont "" []
                              (t :: ts) => cont t ts)
        where
            cont : String -> List String -> (a, List String)
            cont t ts = case k () t of
                             MkStream f => f ts 

--- The Effect and associated functions

STDIO : EFFECT
STDIO = MkEff () StdIO

putStr : Handler StdIO e => String -> Eff e [STDIO] ()
putStr s = PutStr s

putStrLn : Handler StdIO e => String -> Eff e [STDIO] ()
putStrLn s = putStr (s ++ "\n")

getStr : Handler StdIO e => Eff e [STDIO] String
getStr = GetStr

mkStrFn : Env IOStream xs -> 
          Eff IOStream xs a -> 
          List String -> (a, List String)
mkStrFn {a} env p input = case mkStrFn' of
                               MkStream f => f input
  where mkStrFn' : IOStream a
        mkStrFn' = runWith injStream env p
