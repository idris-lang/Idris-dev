interface NumMod where
    number : Bool -> Int

implementation [Five] NumMod where
    number b = 5

foo : NumMod => Int
foo = number True + number False

Increment : Int -> NumMod -> NumMod
Increment inc x = AddOne
   where
     foo : NumMod
     foo = x

     implementation [AddOne] NumMod where
       number x = if x then number@{foo} x + inc else inc

using implementation Five
  main : IO ()
  main = do printLn foo 
            printLn (foo @{Increment 2 Five})
