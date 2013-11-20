module Data.Sign

data Sign = Plus | Minus

class Signed t where
  total sign : t -> Sign
