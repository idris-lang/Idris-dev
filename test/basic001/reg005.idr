module Main

import Data.Vect

%flag C "-g3"
%flag C "-ggdb"
%flag C "-O0"

rep : (n : Nat) -> Char -> Vect n Char
rep Z     x = []
rep (S k) x = x :: rep k x

data RLE : Vect n Char -> Type where
     REnd  : RLE []
     RChar : .{k : Nat}
             -> {xs : Vect k Char}
             -> (n : Nat)
             -> (x : Char)
             -> RLE xs
             -> RLE (rep (S n) x ++ xs)

eq : (x : Char) -> (y : Char) -> Maybe (x = y)
eq x y = if x == y then Just (believe_me (Refl {x})) else Nothing

------------

rle : (xs : Vect n Char) -> RLE xs
rle [] = REnd
rle (x :: xs) with (rle xs)
   rle (x :: Vect.Nil)             | REnd = RChar Z x REnd
   rle (x :: rep (S n) yvar ++ ys) | RChar n yvar rs with (eq x yvar)
     rle (x :: rep (S n) x ++ ys) | RChar n x rs | Just Refl
           = RChar (S n) x rs
     rle (x :: rep (S n) y ++ ys) | RChar n y rs | Nothing
           = RChar Z x (RChar n y rs)

compress : Vect n Char -> String
compress xs with (rle xs)
  compress Nil                 | REnd         = ""
  compress (rep (S n) x ++ xs) | RChar _ _ rs
         = let ni : Integer = cast (S n) in
               show ni ++ strCons x (compress xs)

{-
fmt : {xs : Vect n Char} -> RLE xs -> String
fmt  REnd          = ""
fmt (RChar n c xs) = show n ++ show c ++ fmt xs
-}

compressString : String -> String
compressString xs = compress (fromList (unpack xs))

main : IO ()
main = putStrLn (compressString "foooobaaaarbaaaz")
