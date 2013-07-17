"============================================================================
"File:        idris.vim
"Description: Syntax checking plugin for syntastic.vim
"Maintainer:  raichoo <raichoo at googlemail dot com>
"License:     This program is free software. It comes without any warranty,
"             to the extent permitted by applicable law. You can redistribute
"             it and/or modify it under the terms of the Do What The Fuck You
"             Want To Public License, Version 2, as published by Sam Hocevar.
"             See http://sam.zoy.org/wtfpl/COPYING for more details.
"
"============================================================================

if exists("g:loaded_syntastic_idris_idris_checker")
    finish
endif
let g:loaded_syntastic_idris_idris_checker=1

function! SyntaxCheckers_idris_idris_IsAvailable()
    return executable("idris")
endfunction

if !exists("g:syntastic_idris_options")
    let g:syntastic_idris_options = " "
endif


function! SyntaxCheckers_idris_idris_GetLocList()
    let makeprg = syntastic#makeprg#build({
        \ 'exe': 'idris',
        \ 'args': '--check '. g:syntastic_idris_options,
        \ 'filetype': 'idris',
        \ 'subchecker': 'idris' })

    let errorformat =
        \ '"%f" (line %l\, column %c\):,' .
        \ '%f\:%l\:%m,' .
        \ 'user error (%f\:%l\:%m\)'

    return SyntasticMake({
        \ 'makeprg': makeprg,
        \ 'errorformat': errorformat })
endfunction

call g:SyntasticRegistry.CreateAndRegisterChecker({
    \ 'filetype': 'idris',
    \ 'name': 'idris'})
