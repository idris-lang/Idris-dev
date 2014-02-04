mapFilter : (alpha -> beta) ->
           (alpha -> Bool) -> 
           Vect n alpha -> 
           (n : Nat ** Vect n beta)
mapFilter f p Nil = (_ ** Nil)
mapFilter f p (a :: as) with (p a)
 | True  = (_  ** (f a) :: (getProof (mapFilter f p as)))
 | False = mapFilter f p as


