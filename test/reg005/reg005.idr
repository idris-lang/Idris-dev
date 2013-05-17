module Main

rep : (n : Nat) -> Char -> Vect Char n
rep O     x = []
rep (S k) x = x :: rep k x

data RLE : Vect Char n -> Type where
     REnd  : RLE []
     RChar : {xs : Vect Char k} ->
             (n : Nat) -> (x : Char) -> RLE xs -> 
             RLE (rep (S n) x ++ xs)

eq : (x : Char) -> (y : Char) -> Maybe (x = y)
eq x y = if x == y then Just ?eqCharOK else Nothing

------------

rle : (xs : Vect Char n) -> RLE xs
rle [] = REnd
rle (x :: xs) with (rle xs)
   rle (x :: Vect.Nil)             | REnd = RChar O x REnd
   rle (x :: rep (S n) yvar ++ ys) | RChar n yvar rs with (eq x yvar)
     rle (x :: rep (S n) x ++ ys) | RChar n x rs | Just refl
           = RChar (S n) x rs
     rle (x :: rep (S n) y ++ ys) | RChar n y rs | Nothing 
           = RChar O x (RChar n y rs)

compress : Vect Char n -> String
compress xs with (rle xs)
  compress Nil                 | REnd         = ""
  compress (rep (S n) x ++ xs) | RChar _ _ rs 
         = let ni : Integer = cast (S n) in
               show ni ++ show x ++ compress xs

compressString : String -> String
compressString xs = compress (fromList (unpack xs))

main : IO ()
main = putStrLn (compressString "foooobaaaarbaaaz")



---------- Proofs ----------

Main.eqCharOK = proof {
  intros;
  refine believe_me;
  exact x = x;
}

