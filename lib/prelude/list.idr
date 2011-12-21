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
  | (True, fxs) = x :: fxs; 
  | (False, fxs) = fxs;
}

elem : Eq a => a -> List a -> Bool;
elem x [] = False;
elem x (y :: ys) = if (x == y) then True else (elem x ys);

sort : Ord a => List a -> List a;
sort []  = [];
sort [x] = [x];
sort xs = let s = split xs in
              merge (sort (fst s)) (sort (snd s)) where {
    splitrec : List a -> List a -> (List a -> List a) -> (List a, List a);
    splitrec (_ :: _ :: xs) (y :: ys) zs = splitrec xs ys (zs . ((::) y));
    splitrec _              ys        zs = (zs [], ys);

    split : List a -> (List a, List a);
    split xs = splitrec xs xs id;

    merge : Ord a => List a -> List a -> List a;
    merge xs        []        = xs;
    merge []        ys        = ys;
    merge (x :: xs) (y :: ys) = if (x < y) then (x :: merge xs (y :: ys))
                                           else (y :: merge (x :: xs) ys);
}

span : (a -> Bool) -> List a -> (List a, List a);
span p [] = ([], []);
span p (x :: xs) with p x {
   | True with span p xs {
      | (ys, zs) = (x :: ys, zs);
   }
   | False = ([], x :: xs);
}

break : (a -> Bool) -> List a -> (List a, List a);
break p = span (not . p);
