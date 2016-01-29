module Data.Sign

%access public export

||| A representation of signs for signed datatypes such as `ZZ`
data Sign = Plus | Zero | Minus

||| Discover the sign of some type
interface Signed t where
  total sign : t -> Sign
