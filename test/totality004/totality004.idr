module Main

%default total

data SP : Type -> Type -> Type where
  Get : (a -> SP a b) -> SP a b
  Put : b -> Inf (SP a b) -> SP a b

copy : SP a a
copy = Get (\x => Put x copy)

process : SP a b -> Stream a -> Stream b
process (Get f) (x :: xs) = process (f x) xs
process (Put b sp) xs = b :: process sp xs

doubleInt : SP Nat Int
doubleInt = Get (\x => Put (the Int (cast x)) 
                        (Put (the Int (cast x) * 2) doubleInt))

countStream : Nat -> Stream Nat
countStream x = x :: countStream (x + 1)

main : IO ()
main = printLn (take 10 (process doubleInt (countStream 1)))

