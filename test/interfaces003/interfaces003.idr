interface NumMod where
    number : Bool -> Int

implementation [five] NumMod where
    number b = 5

foo : NumMod => Int
foo = number True + number False

increment : Int -> NumMod -> NumMod
increment inc x = addOne
   where
     foo : NumMod
     foo = x

     implementation [addOne] NumMod where
       number x = if x then number@{foo} x + inc else inc

main : IO ()
main = do printLn (foo @{five})
          printLn (foo @{increment 2 five})
