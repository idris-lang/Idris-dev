
||| class
class C (t : Type) where
  ||| member
  f : t

||| type
data A : Type where
  i : A

||| instance
instance C A where
  f = i
