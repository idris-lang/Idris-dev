data List a = Nil | Cons a (List a);

rev : List a -> List a;
rev xs = revAcc Nil xs
  where {
    revAcc : List a -> List a -> List a;
    revAcc acc Nil = acc;
    revAcc acc (Cons x xs) = revAcc (Cons x acc) xs;
  }

