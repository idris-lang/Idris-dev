
function CaseSplit()
  let view = winsaveview()
  w
  let cline = line(".")
  let word = expand("<cword>")
  let fn = "idris --client :cs! " . cline . " " . word
  let tc = system("idris --client :r")
  if (tc is "")
    let result = system(fn)
    e
    call winrestview(view)
    if (! (result is "")) 
       echo result
    endif
  else
    echo tc
  endif
endfunction

map ci :call CaseSplit()<ENTER>
