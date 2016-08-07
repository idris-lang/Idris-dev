module DoubleEquality

oops : Void
oops = the ((False = True) -> Void) (\Refl impossible) $ cong {f = (>0) . (1/)} $ the (-0.0 = 0.0) Refl

