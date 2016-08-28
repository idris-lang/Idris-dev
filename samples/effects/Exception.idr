module Main

import Effects
import Effect.Exception
import Effect.StdIO
import Control.IOExcept

data MyErr = NotANumber | OutOfRange

implementation Show MyErr where
    show NotANumber = "Not a number"
    show OutOfRange = "Out of range"

parseNumber : Int -> String -> { [EXCEPTION MyErr] } Eff Int
parseNumber num str
   = if all isDigit (unpack str)
        then let x = cast str in
             if (x >=0 && x <= num)
                then pure x
                else raise OutOfRange
        else raise NotANumber
