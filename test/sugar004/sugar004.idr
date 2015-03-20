module Main

import System

total
foo : Maybe Int -> Int
foo x = let Just x' = x | Nothing => 100 in x'

main : IO ()
main = do [p, a] <- getArgs | [p] => putStrLn "No arguments!"
                            | (x :: y :: _) => putStrLn "Too many arguments!"
          printLn (foo (Just (cast a)))

{-

let pat = val | <alternatives> in x'

...becomes...

case val of
     pat => x'
     <alternatives>

do pat <- val | <alternatives>
   p

...becomes...

do x <- val
   case x of
        pat => p
        <alternatives>

-}


