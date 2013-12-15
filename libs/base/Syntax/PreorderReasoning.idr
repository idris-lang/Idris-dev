module Syntax.PreorderReasoning

-- QED is first to get the precedence to work out. It's just refl with an explicit argument.
syntax [expr] "QED" = qed expr
-- foo ={ prf }= bar ={ prf' }= fnord QED
-- is a proof that foo is related to fnord, with the intermediate step being bar, justified by prf and prf'
syntax [from] "={" [prf] "}=" [to] = step from prf to

namespace Equal
  using (a : Type, x : a, y : a, z : a)
    qed : (x : a) -> x = x
    qed x = the (x = x) refl
    step : (x : a) -> x = y -> (y = z) -> x = z
    step x refl refl = refl

