IntString : Bool -> Type
IntString False = Int
IntString True = String

mkString : (str : Bool) -> IntString str -> String
mkString False x = ?mkString_rhs_1
mkString True x = ?mkString_rhs_2

mkThing : (str : Bool) -> IntString str
mkThing False = ?mkThing_rhs_1
mkThing True = ?mkThing_rhs_2

mkString2 : (str : Bool) -> IntString str -> String
mkString2 str x = ?mkString2_rhs

mkString3 : (str : Bool) -> ?what -> String
mkString3 False x = ?mkString3_rhs_1
mkString3 True x = ?mkString3_rhs_2

data Vect : Nat -> Type -> Type where
     Nil : Vect Z a
     (::) : a -> Vect k a -> Vect (S k) a

append : Vect n a -> Vect m a -> Vect (n + m) a
append [] ys = ?append_rhs_1
append (x :: xs) ys = ?append_rhs_2
