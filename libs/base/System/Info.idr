module System.Info

||| The Idris backend in use
export
backend : String
backend = prim__systemInfo 0

||| The operating system in use.
export
os : String
os = prim__systemInfo 1

||| The triple this program was targeted for
export
targetTriple : String
targetTriple = prim__systemInfo 2
