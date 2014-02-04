module Main

-- Simple test case for trivial type providers.

import Providers

%language TypeProviders

strToType : String -> Type
strToType "Int" = Int
strToType _ = Nat

-- If the file contains "Int", provide Int as a type, otherwise provide Nat
fromFile : String -> IO (Provider Type)
fromFile fname = do str <- readFile fname
                    return (Provide (strToType (trim str)))

%provide (T1 : Type) with fromFile "theType"
%provide (T2 : Type) with fromFile "theOtherType"

foo : T1
foo = 2

bar : T2
bar = 2

testFoo : Int
testFoo = foo

testBar : Nat
testBar = bar

