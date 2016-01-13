
decl syntax fun {n} ":" [ty] "=" [def] 
            = n : ty
              n = def

decl syntax newtype {tname} "=" {conname} [tysyn]
     = data tname = conname tysyn

decl syntax EmptyShow {n} =
     implementation Show n where
        show x = "Nothing" 

fun add : (Int -> Int -> Int) = \x, y => x + y

newtype Foo = MkFoo Int 

EmptyShow Foo

main : IO ()
main = do printLn (MkFoo 42)
          printLn (add 3 4)

