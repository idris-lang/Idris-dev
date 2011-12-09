myid : a -> a;
myid x = x;

idid :  (a : Set) -> a -> a;
idid = myid ![myid];

app : (a -> b) -> a -> b;
app f x = f x;

foo : a -> b -> c -> d -> e -> e;
foo a b c d e = e;

doapp : a -> a;
doapp x = app myid x;

{-

id : (b : Set k) -> b -> b : Set l,  k < l

foo = id ((a : Set k) -> a -> a) id
                Set m, k < m

So we have k < m, k < l, m <= k

 when converting Set m against Set n, we must have m <= n
 if we can reach m from n, we have an inconsistency


 -}
