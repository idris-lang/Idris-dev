module Debug.Trace

import Prelude
import IO

trace : String -> a -> a
trace x val = unsafePerformIO (do putStrLn x; return val) 


