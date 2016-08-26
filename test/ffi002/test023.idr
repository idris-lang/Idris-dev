module Main

-- Simple test case for trivial type providers.

%language TypeProviders

-- Provide the Unit type
goodProvider : IO (Provider Type)
goodProvider = pure (Provide (the Type ()))

%provide (Unit' : Type) with goodProvider

foo : Unit'
foo = ()

-- Always fail
badProvider : IO (Provider Type)
badProvider = pure (Error "Always fails")

%provide (t : Type) with badProvider

