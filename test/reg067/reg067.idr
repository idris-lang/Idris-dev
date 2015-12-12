module Main

-- https://github.com/idris-lang/Idris-dev/issues/2844
main_2844 : IO ()
main_2844 =
  let
    f =
      the
        ((String,String) -> String -> (String, Maybe String ))
        (\(_,s),y => (s, Just s))
  in
    case snd $ f ("tst","tst2") "cenas" of
      Just z => putStr z

-- https://github.com/idris-lang/Idris-dev/issues/2493
main_2493 : IO ()
main_2493 = printLn $ doThing [1,2,3] [("as",1),("asasasas",4)]
  where
    doThing : List Nat -> List (v,Nat) -> List v
    doThing is g = foldr (\(v,i),res => if elem i is then v::res else res) List.Nil g

main : IO ()
main = main_2844 *> main_2493
