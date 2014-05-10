module Data.List

%access public

using (xs : List a)
  ||| A proof that some element is found in a list
  data Elem : a -> List a -> Type where
       Here : Elem x (x :: xs)
       There : Elem x xs -> Elem x (y :: xs)
  
  instance Uninhabited (Elem {a} x []) where
       uninhabited Here impossible
       uninhabited (There p) impossible
 
  private
  mkNo : ((x = y) -> _|_) -> (Elem x xs -> _|_) -> Elem x (y :: xs) -> _|_
  mkNo f g Here = f refl
  mkNo f g (There x) = g x

  isElem : DecEq a => (x : a) -> (xs : List a) -> Dec (Elem x xs)
  isElem x [] = No absurd
  isElem x (y :: xs) with (decEq x y)
    isElem x (x :: xs) | (Yes refl) = Yes Here
    isElem x (y :: xs) | (No contra) with (isElem x xs)
      isElem x (y :: xs) | (No contra) | (Yes prf) = Yes (There prf)
      isElem x (y :: xs) | (No contra) | (No f) = No (mkNo contra f)
  

