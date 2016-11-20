import Data.Fin

%default total

foo : Fin 3 -> Nat
foo FZ = 0
foo (FS FZ) = 1
foo (FS (FS FZ)) = 2
-- testing that there is no need for an extra 'impossible'

bar : Fin 4 -> Nat
bar FZ = 0
bar (FS FZ) = 1
bar (FS (FS FZ)) = 2
-- should be non-total
