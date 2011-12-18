
vapp : Vect a n -> Vect a m -> Vect a (n + m);
vapp Nil       ys = ys;
vapp (x :: xs) ys = x :: vapp xs xs; -- BROKEN


