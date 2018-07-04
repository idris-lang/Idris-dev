{-
See: http://lpaste.net/104020
  and https://github.com/gonzaw/extensible-records
-}
module Record

import Data.List

%default total

data HList : List Type -> Type where
  Nil : HList []
  (::) : a -> HList xs -> HList (a :: xs)

infix 5 :=

data Field : lbl -> Type -> Type where
  (:=) : (label : lbl) ->
          (value : b) -> Field label b

labelsOf : List (lbl, Type) -> List lbl
labelsOf [] = []
labelsOf ((label, _) :: xs) = label :: labelsOf xs

toFields : List (lbl, Type) -> List Type
toFields [] = []
toFields ((l, t) :: xs) = (Field l t) :: toFields xs

data IsSet : List t -> Type where
  IsSetNil : IsSet []
  IsSetCons : Not (Elem x xs) -> IsSet xs -> IsSet (x :: xs)

data Record : List (lty, Type) -> Type where
  MkRecord : IsSet (labelsOf ts) -> HList (toFields ts) ->
                                    Record ts

infixr 6 +:

rnil : Record []
rnil = MkRecord IsSetNil []

prepend : { label : lbl,
          xs : List (lbl, Type),
          prf : Not (Elem label (labelsOf xs))
        } ->
        Field label t ->
        Record xs ->
        Record ((label, t) :: xs)
prepend {prf} f (MkRecord isSet fs) = MkRecord (IsSetCons prf isSet) (f :: fs)

data IsNo : Dec prop -> Type where
  ItIsNo : IsNo (No yprf)

(+:) : DecEq lbl =>
  { label : lbl, xs : List (lbl, Type) } ->
  Field label t ->
  Record xs ->
  { auto isno : IsNo (isElem label $ labelsOf xs) } ->
  Record ((label, t) :: xs)

(+:) {label} {xs} f r with (isElem label $ labelsOf xs)
    (+:) { isno = ItIsNo } _ _ | (Yes _) impossible
    (+:) f r | (No no) = prepend {prf = no} f r

foo : Record [("Year", Integer)]

bar : Record [("Title", String), ("Year", Integer)]
bar = (+:) ("Title" := "test") foo

