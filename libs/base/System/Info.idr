module System.Info

||| The Idris backend in use
backend : String
backend = prim__systemInfo 0

||| The operating system in use.
os : String
os = prim__systemInfo 1

||| The triple this program was targeted for
targetTriple : String
targetTriple = prim__systemInfo 2
