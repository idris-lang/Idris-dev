data Ty = Ctor Int

total
fn : Ty -> Ty
fn m@(Ctor _) = y
  where
    y = m

asPatternVisibleInWhere : fn (Ctor 42) = Ctor 42
asPatternVisibleInWhere = Refl

main : IO ()
main = putStrLn "OK"
