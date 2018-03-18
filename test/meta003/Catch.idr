import Language.Reflection.Elab

%language ElabReflection

f : Err -> Elab ()
f (Msg _) = fill `("message error")
f (CantUnify _ _ _ _ _ _) = fill `("unification error")
f _ = fill `("other")

s1 : String
s1 = %runElab (do tryCatch (fail []) f ; solve)

s2 : String
s2 = %runElab (do tryCatch (fill `(True)) f ; solve)

main : IO ()
main = do putStrLn s1 ; putStrLn s2
