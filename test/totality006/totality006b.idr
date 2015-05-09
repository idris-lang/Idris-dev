module totality006b

import Data.So


-- There are approaches to impossibility checking that break on this
-- case but not on test006.idr, due to the extra computation.
total
blargh : (xs, ys : List a) -> So (length xs > length ys) -> GT (length xs) (length ys)
blargh [] (y :: xs) so = absurd so
blargh (y :: xs) [] Oh = LTESucc LTEZero

-- Missing: blargh (y :: xs) (z :: ys) p = ?blargh_rhs_3
-- blargh [] [] p = ?foo -- impossible
