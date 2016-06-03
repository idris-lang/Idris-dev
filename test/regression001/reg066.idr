foo : Reflection.Raw -> Bool
foo `(~_ -> ~_) = True
foo _ = False

foo' : TT -> Bool
foo' `(~_ -> ~_) = True
foo' _ = False
