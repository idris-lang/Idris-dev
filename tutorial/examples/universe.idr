myid : (a : Set) -> a -> a
myid _ x = x

idid :  (a : Set) -> a -> a
idid = myid _ myid


