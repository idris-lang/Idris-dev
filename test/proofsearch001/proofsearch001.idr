%default total

class C a (f : Bool -> Bool) | a where {}
instance C Int not where {}

foo : C Int g => {auto pf : g True = False} -> Unit
foo = ()

main : IO ()
main = printLn $ foo -- {pf = Refl}

