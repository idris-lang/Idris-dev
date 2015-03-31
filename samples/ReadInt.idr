module ReadInt

import Effects
import Effect.State
import Effect.StdIO

readInt : { [STATE (Vect n Int), STDIO] ==>
            {ok} if ok then [STATE (Vect (S n) Int), STDIO]
                       else [STATE (Vect n Int), STDIO] } Eff Bool
readInt = do let x = trim !getStr
             case all isDigit (unpack x) of
                  False => pure False
                  True => do updateM (\xs => cast x ::xs)
                             pure True

readN : (n : Nat) ->
        { [STATE (Vect m Int), STDIO] ==>
          [STATE (Vect (n + m) Int), STDIO] } Eff ()
readN Z = pure ()
readN {m} (S k) = case !readInt of
                      True => rewrite plusSuccRightSucc k m in readN k
                      False => readN (S k)
