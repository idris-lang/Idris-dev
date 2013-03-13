module Core.Execute where

import Core.TT
import Core.Evaluate

-- | Attempt to perform a side effect. Return either Just the next step in
-- evaluation (after performing the side effect through IO), or Nothing if no
-- IO was performed.
execute :: TT Name -> Idris (Maybe (TT Name))
execute tm = Nothing