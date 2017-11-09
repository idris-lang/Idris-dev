-- ---------------------------------------------------------- [ Assertions.idr ]
-- Module    : Assertions.idr
-- Copyright : (c) The Idris Community
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
||| Some simple assertions.
module Test.Unit.Assertions

import Test.Unit.Generic

%access export

assertTrue : (given : Bool) -> IO Bool
assertTrue b = genericTest (Just "Assert True") b True (==)

assertFalse : (given : Bool) -> IO Bool
assertFalse b = genericTest (Just "Assert False") b False (==)

assertEquals : (Eq a, Show a) => (given : a) -> (expected : a) -> IO Bool
assertEquals g e = genericTest (Just "Assert Equals") g e (==)

assertNotEquals : (Eq a, Show a) => (given : a) -> (expected : a) -> IO Bool
assertNotEquals g e = genericTest (Just "Assert Not Equals") g e (\x,y => not (x == y))

assertJust : Show a => (given : Maybe a) -> IO Bool
assertJust g = genericTest (Just "Assert Is Just") (isJust g) True (==)

assertNothing : Show a => (given : Maybe a) -> IO Bool
assertNothing g = genericTest (Just "Assert Is Nothing") (isNothing g) True (==)

assertLeft : (Show a, Show b) => (given : Either a b) -> IO Bool
assertLeft g = genericTest (Just "Assert is Left") (isLeft g) True (==)

assertRight : (Show a, Show b) => (given : Either a b) -> IO Bool
assertRight g = genericTest (Just "Assert is Right") (isRight g) True (==)

-- --------------------------------------------------------------------- [ EOF ]
