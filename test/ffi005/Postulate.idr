module Main

%language TypeProviders

bad : IO (Provider Type)
bad = pure $ pure Void

%provide postulate oops with bad

main : IO ()
main = putStrLn "oops"

