" syntax highlighting for idris (idris-lang.org)
"
" Heavily modified version of the haskell syntax 
" highlighter to support idris.
"
" author: raichoo (raichoo@googlemail.com)
" date: Sep 21 2012

syn match idrisModule "\<\(module\|namespace\)\>"
syn match idrisImport "\<import\>"
syn match idrisStructure "\<\(class\|data\|instance\|where\|record\)\>"
syn match idrisVisibility "\<\(public\|abstract\|private\)\>"
syn match idrisStatement "\<\(do\|case\|of\|let\|in\|with\|total\|dsl\|auto\|using\|parameters\)\>"
syn match idrisSyntax "\(pattern \+\|term \+\)\?syntax"
syn match idrisConditional "\<\(if\|then\|else\)\>"
syn match idrisTactic contained "\<\(intros\?\|rewrite\|exact\|refine\|trivial\|let\|focus\|try\|compute\|solve\|attack\)\>"
syn match idrisNumber "\<[0-9]\+\>\|\<0[xX][0-9a-fA-F]\+\>\|\<0[oO][0-7]\+\>"
syn match idrisFloat "\<[0-9]\+\.[0-9]\+\([eE][-+]\=[0-9]\+\)\=\>"
syn match idrisDelimiter  "(\|)\|\[\|\]\|,\|;\|_\|{\|}"
syn match idrisInfix "\<\(prefix\|infix\|infixl\|infixr\)\>"
syn match idrisOperators "\([-!#$%&\*\+./<=>\?@\\^|~:]\|\<_\>\)"
syn match idrisType "\<\([A-Z][a-zA-Z0-9_]*\|_|_\)\>"
syn match idrisLineComment "---*\([^-!#$%&\*\+./<=>\?@\\^|~].*\)\?$"
syn match idrisMetaVar "?[a-z][A-Za-z0-9_]\+"
syn match idrisLink "%\(lib\|link\|include\)"
syn match idrisAccess "%access"
syn region idrisString start=+"+ skip=+\\\\\|\\"+ end=+"+
syn region idrisBlockComment start="{-" end="-}"
syn region idrisProofBlock start="\(default\s\+\)\?proof *{" end="}" contains=idrisTactic

highlight def link idrisImport Include
highlight def link idrisModule idrisStructure
highlight def link idrisStructure Structure
highlight def link idrisStatement Statement
highlight def link idrisSyntax Statement
highlight def link idrisVisibility Statement
highlight def link idrisConditional Conditional
highlight def link idrisProofBlock Macro
highlight idrisTactic ctermfg=cyan
highlight idrisLink ctermbg=yellow ctermfg=magenta
highlight idrisAccess ctermbg=magenta ctermfg=yellow
highlight def link idrisNumber Number
highlight def link idrisFloat Float
highlight def link idrisDelimiter Delimiter
highlight def link idrisInfix PreProc
highlight def link idrisOperators Operator
highlight def link idrisType Type
highlight def link idrisLineComment Comment
highlight def link idrisBlockComment Comment
highlight idrisMetaVar ctermbg=cyan ctermfg=black
highlight def link idrisString String
