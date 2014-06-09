module Main

import Providers

%language TypeProviders

bad : IO (Provider Type)
bad = return $ pure _|_

%provide postulate oops with bad

main : IO ()
main = putStrLn "oops"

