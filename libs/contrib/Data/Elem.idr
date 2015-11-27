module Data.Elem

%default total

data Elem : a -> List a -> Type where
  Here : Elem x (x :: xs)
  There : Elem x xs -> Elem x (y :: xs)

instance DecEq (Elem x xs) where
  decEq Here Here = Yes Refl
  decEq Here (There _) = No (\Refl impossible)
  decEq (There _) Here = No (\Refl impossible)
  decEq (There x) (There y) =
    case x `decEq` y of
      Yes prf => Yes (cong prf)
      No f => No (\Refl => f Refl)

instance Uninhabited (Elem x []) where
  uninhabited Here impossible
  uninhabited (There _) impossible

decElem : DecEq a => (x : a) -> (xs : List a) -> Dec (Elem x xs)
decElem _ [] = No absurd
decElem y (x :: xs) =
  case x `decEq` y of
    Yes Refl => Yes Here
    No prfNotEq =>
      case decElem y xs of
        Yes prfElem => Yes (There prfElem)
        No prfNotElem => No (\v =>
          case v of
            There c => prfNotElem c
            Here => prfNotEq Refl)

position : Elem xs x -> Nat
position Here = 0
position (There p) = 1 + position p

positionInBounds : (prf : Elem x xs) -> InBounds (position prf) xs
positionInBounds Here = InFirst
positionInBounds (There p) = InLater (positionInBounds p)

lookupElemEq : (prf:Elem x xs) -> index (position prf) xs {ok=positionInBounds prf} = x
lookupElemEq Here = Refl
lookupElemEq (There p) = lookupElemEq p

createElemFromIndexProof : index n xs {ok} = x -> Elem x xs
createElemFromIndexProof Refl {ok=InFirst} = Here
createElemFromIndexProof Refl {ok=InLater _} = There (createElemFromIndexProof Refl)
