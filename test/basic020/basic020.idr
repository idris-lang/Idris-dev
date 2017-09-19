%default total

data Ty = Ctor Int

fn : Ty -> Ty
fn m@(Ctor _) = y
  where
    y = m -- from @ pattern

asPatternVisibleInWhere : fn (Ctor 42) = Ctor 42
asPatternVisibleInWhere = Refl

fn2 : Ty -> Ty
fn2 m@(Ctor _) = y (Ctor 99)
  where
    y m = m -- should be the arg `m`, not the @ pattern

lhsVariablesShadowAsPattern : fn2 (Ctor 42) = Ctor 99
lhsVariablesShadowAsPattern = Refl

fn3 : Ty -> Ty
fn3 m@(Ctor _) = y (Ctor 99)
  where
    y m = z
      where
        z = m -- should be y's arg `m`, not @ pattern

nestedWhereShadowsAsPattern : fn3 (Ctor 42) = Ctor 99
nestedWhereShadowsAsPattern = Refl

fn4 : Ty -> Ty
fn4 m@(Ctor _) = y (Ctor 99)
  where
    y _ = z
      where
        z = m -- should be @ pattern

nestedWhereExposesAsPattern : fn4 (Ctor 42) = Ctor 42
nestedWhereExposesAsPattern = Refl

main : IO ()
main = putStrLn "OK"
