module IRTS.Defunctionalise where

import IRTS.Lang
import Core.TT

defunctionalise :: [(Name, LDecl)] -> [(Name, LDecl)]
defunctionalise defs = defs -- TODO!

-- To defunctionalise:
--
-- 1 Create a data constructor for each function
-- 2 Create a data constructor for each underapplication of a function
-- 3 Convert underapplications to their corresponding constructors
-- 4 Create an EVAL function which calls the appropriate function for data constructors
--   created as part of step 1
-- 5 Create an APPLY function which adds an argument to each underapplication (or calls
--   APPLY again for an exact application)
-- 6 Wrap overapplications in chains of APPLY


