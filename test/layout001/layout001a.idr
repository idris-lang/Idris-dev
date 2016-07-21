-- This file passes the parser but should fail
f : Int -> Int
f x = z 1 + 1 where
  z : Int -> Int
  z y =
y -- FIXME: Should fail on this line with a layout-rule error.
