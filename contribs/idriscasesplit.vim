
function CaseSplit()
  let view = winsaveview()
  w
  let cline = line(".")
  let word = expand("<cword>")
  let fn = "idris --client :cs! " . cline . " " . word
  let tc = system("idris --client :r")
  let result = system(fn)
  e
  call winrestview(view)
  if (! (result is "")) 
     echo result
  endif
endfunction

map ci :call CaseSplit()<ENTER>
