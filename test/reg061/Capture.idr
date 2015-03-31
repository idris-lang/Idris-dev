module Capture

-- Test for variable capture in syntax

syntax delay  [x] = \z => case z of { () => x }
syntax delay' [z] = delay z

capture : a -> () -> a
capture x = delay' x
