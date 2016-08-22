elimId : (a : Type) ->
         (a1 : a) ->
         (a2 : a) ->
         (m : (x : a) -> (y : a) -> x = y -> Type) ->
         (f : (x : a) -> m x x Refl) ->
         (id : a1 = a2) ->
         m a1 a2 id
elimId _ x _ _ f Refl = f x

tran : (a : Type) -> (b : a) -> (c : a) -> (d : a) ->  
       (e : b = c) ->  (f : c = d) ->  b = d
tran = \ a : Type , b : a , c : a , d : a , e : b = c =>
    (elimId a b c (\ f : a , g : a , h : f = g => 
                         (i : a) ->  (j : g = i) ->  f = i)
                 (\ f : a , g : a , h : f = g =>  h) e d)
