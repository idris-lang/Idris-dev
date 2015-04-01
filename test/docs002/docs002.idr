module Main

-- Simple test case for type provider documentation.
%language TypeProviders

getType : Int -> IO (Provider Type)
getType 0 = return (Provide Int)
getType _ = return (Provide Bool)

||| Some documentation
%provide (T1 : Type) with getType 0

||| Some other documentation
%provide (T2 : Type) with getType 1

||| Some provided postulate
%provide postulate T3 with getType 0
