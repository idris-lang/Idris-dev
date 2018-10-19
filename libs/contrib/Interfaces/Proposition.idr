module Interfaces.Proposition

%default total
%access public export


||| A canonical proof that some type containing no more than one value,
||| comprising a mere proposition.
interface Proposition t where
  ||| If there are two values of t, prove that they are actually the same
  atMostOneValue : (x : t) -> (y : t) -> x = y

Proposition () where
  atMostOneValue () () = Refl

Proposition Void where
  atMostOneValue _ _ impossible
  
Proposition (x = y) where
  atMostOneValue Refl Refl = Refl

Proposition (LTE m n) where
  atMostOneValue {m=Z} LTEZero LTEZero = Refl
  atMostOneValue {m=S _} (LTESucc x) (LTESucc y) = cong $ atMostOneValue x y
  
Proposition (NonEmpty xs) where
  atMostOneValue IsNonEmpty IsNonEmpty = Refl

(Proposition a, Proposition b) => Proposition (a, b) where
  atMostOneValue (x1, y1) (x2, y2) =
    rewrite atMostOneValue x1 x2 in
      rewrite atMostOneValue y1 y2 in Refl