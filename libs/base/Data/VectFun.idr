module Data.VectFun

VectFun : Vect n Type -> Type -> Type
VectFun [] r = r
VectFun (t::ts) r = t -> VectFun ts r
