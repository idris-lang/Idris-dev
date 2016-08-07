module working

-- Check that using an operator beginning with "!" works

infixl 2 !!

(!!) : List a -> Nat -> Maybe a
xs !! n = index' n xs

aList : List Integer
aList = [1,2,3,4,5]

opUse : Maybe Integer
opUse = aList !! 2

opUseWithBang : Maybe Nat -> Maybe Integer
opUseWithBang mn = do aList !! !mn

doubleBang : Maybe (Maybe Nat) -> Maybe Nat
doubleBang mmn = do pure ! !mmn

