module Data.Sign

%access public export

||| A representation of signs for signed datatypes such as `ZZ`
data Sign = Plus | Zero | Minus

opposite : Sign -> Sign
opposite Plus  = Minus
opposite Zero  = Zero
opposite Minus = Plus

multiply : Sign -> Sign -> Sign
multiply Zero  _    = Zero
multiply _     Zero = Zero
multiply Plus  x    = x
multiply Minus x    = opposite x

||| Discover the sign of some type
interface Signed t where
  total sign : t -> Sign

Signed Int where
  sign x with (compare x 0)
    | LT = Minus
    | EQ = Zero
    | GT = Plus

Signed Integer where
  sign x with (compare x 0)
    | LT = Minus
    | EQ = Zero
    | GT = Plus

Signed Double where
  sign x with (compare x 0.0)
    | LT = Minus
    | EQ = Zero
    | GT = Plus
