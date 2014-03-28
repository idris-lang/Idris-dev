module Main

%default total

data SP : Type -> Type -> Type where
  get : (a -> SP a b) -> SP a b
  put : b -> Inf (SP a b) -> SP a b

copy : SP a a
copy = get (\x => put x copy)

process : SP a b -> Stream a -> Stream b
process (get f) (x :: xs) = process (f x) xs
process (put b sp) xs = b :: process sp xs

doubleInt : SP Nat Int
doubleInt = get (\x => put (the Int (cast x)) 
                        (put (the Int (cast x) * 2) doubleInt))

countStream : Nat -> Stream Nat
countStream x = x :: countStream (x + 1)

main : IO ()
main = print (take 10 (process doubleInt (countStream 1)))

