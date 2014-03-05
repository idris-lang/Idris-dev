module Main

import Providers

%language TypeProviders

bad : IO (Provider _|_)
bad = pure Postulate

%provide term (oops : _|_) with bad

main : IO ()
main = putStrLn "oops"
