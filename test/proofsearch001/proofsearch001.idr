%default total

interface C a (f : Bool -> Bool) | a where {}
implementation C Int Bool.not where {}

foo : C Int g => {auto pf : g True = False} -> Unit
foo = ()

main : IO ()
main = printLn $ foo -- {pf = Refl}

