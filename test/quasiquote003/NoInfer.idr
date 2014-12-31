module NoInfer

import Language.Reflection
import Language.Reflection.Utils
import Data.Fin

zzz2 : TT
zzz2 = `(FZ : Fin 3)

zzz : TT
zzz = `(FZ)
