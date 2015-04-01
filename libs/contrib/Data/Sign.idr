module Data.Sign

||| A representation of signs for signed datatypes such as `ZZ`
data Sign = Plus | Zero | Minus

||| Discover the sign of some type
class Signed t where
  total sign : t -> Sign
