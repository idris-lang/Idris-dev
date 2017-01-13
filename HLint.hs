{-# LANGUAGE TemplateHaskell #-}
--  --------------------------------------------------------------- [ HLint.hs ]
-- HLint suggestions we like.
--
-- This is a work in progress and the list of
-- suggestions/warnings/errors will vary.
--
--  -------------------------------------------------------------------- [ EOH ]

-- import "hint" HLint.HLint -- In case we want to use all of them.

--  ------------------------------------------------------------ [ Suggestions ]
-- Styling that are good Suggestions but are okay if found.

suggest "Use exitSuccess"
suggest "Use concatMap"
suggest "Use unwords"
suggest "Use null"
suggest "Redundant $"
suggest "Use list literal pattern"
suggest "Use list literal"

--  ------------------------------------------------------------------- [ Warn ]
-- Styling that we think a programmer should be warned about using.


--  ------------------------------------------------------------------ [ Error ]
-- Styling that we think a programmer should not use at all.


--  ----------------------------------------------------------------- [ Ignore ]
-- Suggestions we want to ignore.

--  -------------------------------------------------------------------- [ EOF ]
