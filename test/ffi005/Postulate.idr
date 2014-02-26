module Postulate

import Providers

%language TypeProviders

bad : IO (Provider _|_)
bad = pure Postulate

%provide (oops : _|_) with bad

namespace Main
  main : IO ()
  main = putStrLn "oops"

