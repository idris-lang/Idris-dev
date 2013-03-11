" syntax highlighting for idris (idris-lang.org)
"
" Heavily modified version of the haskell syntax 
" highlighter to support idris.
"
" author: raichoo (raichoo@googlemail.com)
" date: Feb 25 2013

syn match idrisModule "\<\(module\|namespace\)\>"
syn match idrisImport "\<import\>"
syn match idrisStructure "\<\(class\|\(co\)\?data\|instance\|where\|record\|dsl\)\>"
syn match idrisVisibility "\<\(public\|abstract\|private\)\>"
syn match idrisBlock "\<\(parameters\|mutual\|postulate\|using\)\>"
syn match idrisAnnotation "\<\(total\|partial\|auto\|impossible\|static\|implicit\)\>"
syn match idrisStatement "\<\(do\|case\|of\|let\|in\|with\)\>"
syn match idrisSyntax "\(pattern \+\|term \+\)\?syntax"
syn match idrisConditional "\<\(if\|then\|else\)\>"
syn match idrisTactic contained "\<\(intros\?\|rewrite\|exact\|refine\|trivial\|let\|focus\|try\|compute\|solve\|attack\|reflect\)\>"
syn match idrisNumber "\<[0-9]\+\>\|\<0[xX][0-9a-fA-F]\+\>\|\<0[oO][0-7]\+\>"
syn match idrisFloat "\<[0-9]\+\.[0-9]\+\([eE][-+]\=[0-9]\+\)\=\>"
syn match idrisDelimiter  "(\|)\|\[\|\]\|,\|;\|_\|{\|}"
syn match idrisInfix "\<\(prefix\|infix\|infixl\|infixr\)\>"
syn match idrisOperators "\([-!#$%&\*\+./<=>\?@\\^|~:]\|\<_\>\)"
syn match idrisType "\<\([A-Z][a-zA-Z0-9_]*\|_|_\)\>"
syn match idrisLineComment "---*\([^-!#$%&\*\+./<=>\?@\\^|~].*\)\?$"
syn match idrisMetaVar "?[a-z][A-Za-z0-9_]\+"
syn match idrisLink "%\(lib\|link\|include\)"
syn match idrisDirective "%\(access\|default\|assert_total\)"
syn region idrisString start=+"+ skip=+\\\\\|\\"+ end=+"+
syn region idrisBlockComment start="{-" end="-}"
syn region idrisProofBlock start="\(default\s\+\)\?proof *{" end="}" contains=idrisTactic

syn match idrisBadLeadingWhiteSpace "^\s*\t\+"
syn match idrisBadTrailingWhiteSpace "\s\+$"

highlight idrisBadLeadingWhiteSpace ctermbg=red
highlight idrisBadTrailingWhiteSpace ctermbg=red

highlight def link idrisImport Structure
highlight def link idrisModule Structure
highlight def link idrisStructure Structure
highlight def link idrisStatement Statement
highlight def link idrisBlock Statement
highlight def link idrisAnnotation Statement
highlight def link idrisSyntax Statement
highlight def link idrisVisibility Statement
highlight def link idrisConditional Conditional
highlight def link idrisProofBlock Macro
highlight idrisTactic ctermfg=cyan
highlight def link idrisLink Statement
highlight def link idrisDirective Statement
highlight def link idrisNumber Number
highlight def link idrisFloat Float
highlight def link idrisDelimiter Delimiter
highlight def link idrisInfix PreProc
highlight def link idrisOperators Operator
highlight def link idrisType Include
highlight def link idrisLineComment Comment
highlight def link idrisBlockComment Comment
highlight idrisMetaVar ctermfg=red
highlight def link idrisString String
