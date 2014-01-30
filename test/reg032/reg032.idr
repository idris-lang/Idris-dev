module reg032

zfin : Fin 1
zfin = 0

data Infer = MkInf a

foo : Infer
foo = MkInf (the (Fin 1) 0)

