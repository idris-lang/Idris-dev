module badbangop

-- Check that using "!" by itself as an operator does not work

infixl 2 !

(!) : List a -> Nat -> Maybe a
xs ! n = index' n xs

aList : List Integer
aList = [1,2,3,4,5]

opUse : Maybe Integer
opUse = aList ! 2

