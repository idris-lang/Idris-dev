" indentation for idris (idris-lang.org)
" 
" Based on haskell indentation by motemen <motemen@gmail.com>
" 
" author: raichoo (raichoo@googlemail.com)
" date: Sep 21 2012 
"
" Modify g:idris_indent_if and g:idris_indent_case to
" change indentation for `if'(default 3) and `case'(default 5).
" Example (in .vimrc):
" > let g:idris_indent_if = 2

if exists('b:did_indent')
    finish
endif

let b:did_indent = 1

if !exists('g:idris_indent_if')
    " if bool
    " >>>then ...
    " >>>else ...
    let g:idris_indent_if = 3
endif

if !exists('g:idris_indent_case')
    " case xs of
    " >>>>>[] -> ...
    " >>>>>(y:ys) -> ...
    let g:idris_indent_case = 5
endif

setlocal indentexpr=GetIdrisIndent()
setlocal indentkeys=!^F,o,O

function! GetIdrisIndent()
    let line = substitute(getline(getpos('.')[1] - 1), '\t', repeat(' ', &tabstop), 'g')

    if line =~ '[!#$%&*+./<=>?@\\^|~-]$\|\<do$'
        return match(line, '\s*where \zs\|\S') + &shiftwidth
    endif

    if line =~ '{$'
        return match(line, '\s*where \zs\|\S') + &shiftwidth
    endif

    if line =~ '^\s*\(data\|instance\|class\).*\&.*where$'
        return match(line, '\(data\|instance\|class\)') + &shiftwidth
    endif

    if line =~ '^\s*using\s*(.\+)$'
        return match(line, 'using') + &shiftwidth
    endif

    if line =~ '\<with\>'
      return &shiftwidth
    endif

    if line =~ '^\s*data\s\+\S*\s\+=\s\+\S\+$'
      return match(line, '=')
    endif

    if line =~ '^\s*namespace\s\+\S\+$'
      return match(line, 'namespace') + &shiftwidth
    endif

    if line =~ ')$'
        let pos = getpos('.')
        normal k$
        let paren_end   = getpos('.')
        normal %
        let paren_begin = getpos('.')
        call setpos('.', pos)
        if paren_begin[1] != paren_end[1]
            return paren_begin[2] - 1
        endif
    endif

    if line !~ '\<else\>'
        let s = match(line, '\<if\>.*\&.*\zs\<then\>')
        if s > 0
            return s
        endif

        let s = match(line, '\<if\>')
        if s > 0
            return s + g:idris_indent_if
        endif
    endif

    let s = match(line, '\<do\s\+\zs[^{]\|\<where\s\+\zs\w\|\<let\s\+\zs\S\|^\s*\zs|\s')
    if s > 0
        return s
    endif

    let s = match(line, '\<case\>')
    if s > 0
        return s + g:idris_indent_case
    endif

    return match(line, '\S')
endfunction
