module Main

foo : { t : Type } ->
      (a : t) ->
      { default tactics { refine refl; solve; } prfA : a = a } ->
      (b : Nat) ->
      (c : Nat) ->
      { default tactics { refine refl; solve; } prfBC : b = c } ->
      Nat
foo {t} a {prfA = p} b c {prfBC} = b

main : IO ()
main = print $ foo 3 4 4
