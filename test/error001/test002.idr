myid : (a : Type) -> a -> a
myid _ x = x

idid :  (a : Type) -> a -> a
idid = myid _ myid

app : (a -> b) -> a -> b
app f x = f x

foo : a -> b -> c -> d -> e -> e
foo a b c d e = e

doapp : a -> a
doapp x = app (myid _) x

{-

id : (b : Type k) -> b -> b : Type l,  k < l

foo = id ((a : Type k) -> a -> a) id
                Type m, k < m

So we have k < m, k < l, m <= k

 when converting Type m against Type n, we must have m <= n
 if we can reach m from n, we have an inconsistency


 -}
