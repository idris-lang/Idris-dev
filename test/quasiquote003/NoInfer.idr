module NoInfer

import Language.Reflection
import Language.Reflection.Utils

zzz2 : TT
zzz2 = `(fZ : Fin 3)

zzz : TT
zzz = `(fZ)
