module Main

-- Simple test case for trivial type providers.

import Providers

%language TypeProviders

-- Provide the Unit type
goodProvider : Provider Type
goodProvider = Provide (return (the Type ()))

%provide (Unit : Type) with goodProvider

foo : Unit
foo = ()

-- Always fail
badProvider : Provider Type
badProvider = Error (return "Always fails")

%provide (t : Type) with badProvider

