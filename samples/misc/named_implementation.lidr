> module MyOrd

An alternative Ord implementation for Nats, with an explicit name "myord"
for the dictionary:

> implementation [myord] Ord Nat where
>    compare O (S n)     = GT
>    compare (S n) O     = LT
>    compare O O         = EQ

The @{name} syntax below gives an explicit dictionary for the compare function.
Here, we're telling it to use the "myord" dictionary. Otherwise, it'd just
use the default (unnamed) implementation. Note that there can only be one unnamed
implementation --- they must not overlap.

>    compare (S x) (S y) = compare @{myord} x y

> foo : List Nat
> foo = [1,4,2,8,3,7,5,6]

Sort foo using the default comparison operator:

> test1 : List Nat
> test1 = sort foo

-- which gives [1,2,3,4,5,6,7,8]

Sort foo using the alternative implementation. No need for 'sortBy' and other
such functions. Hoorah!

> test2 : List Nat
> test2 = sort @{myord} foo

-- which gives [8,7,6,5,4,3,2,1]


