module Main

import A as X
import B.C as Y

checkX : X.num = Z
checkX = refl

checkY : Y.num = S Z
checkY = refl

checkAX : X.num = A.num
checkAX = refl

checkBY : Y.num = B.C.num
checkBY = refl
