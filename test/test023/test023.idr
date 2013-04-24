module Main

-- Simple test case for trivial type providers.

import Providers

%language TypeProviders

-- Provide the Unit type
goodProvider : IO (Provider Type)
goodProvider = return (Provide (the Type ()))

%provide (Unit : Type) with goodProvider

foo : Unit
foo = ()

-- Always fail
badProvider : IO (Provider Type)
badProvider = return (Error "Always fails")

%provide (t : Type) with badProvider

