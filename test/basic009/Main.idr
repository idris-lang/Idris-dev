module Main

import A as X
import B.C as Y

checkX : X.num = Z
checkX = Refl

checkY : Y.num = S Z
checkY = Refl

checkAX : X.num = A.num
checkAX = Refl

checkBY : Y.num = B.C.num
checkBY = Refl
