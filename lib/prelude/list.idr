module prelude.list;

import builtins;

infixr 7 :: ;

data List a = Nil | (::) a (List a);

rev : List a -> List a;
rev xs = revAcc [] xs where {
  revAcc : List a -> List a -> List a;
  revAcc acc [] = acc;
  revAcc acc (x :: xs) = revAcc (x :: acc) xs;
}

length : List a -> Int;
length []        = 0;
length (x :: xs) = 1 + length xs;

take : Int -> List a -> List a;
take 0 xs = [];
take n [] = [];
take n (x :: xs) = x :: take (n-1) xs;

drop : Int -> List a -> List a;
drop 0 xs = xs;
drop n [] = [];
drop n (x :: xs) = drop (n-1) xs;

map : (a -> b) -> List a -> List b;
map f []        = [];
map f (x :: xs) = f x :: map f xs;

filter : (y -> Bool) -> List y -> List y;
filter pred [] = [];
filter pred (x :: xs) with (pred x, filter pred xs) {
  filter pred (x :: xs) | (True, fxs) = x :: fxs; 
  filter pred (x :: xs) | (False, fxs) = fxs;
}

