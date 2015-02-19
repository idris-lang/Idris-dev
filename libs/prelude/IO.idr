%unqualified

import Builtins
import Prelude.List

%access public

||| Idris's primitive IO, for building abstractions on top of
abstract 
data PrimIO : Type -> Type where
     prim__IO : a -> PrimIO a

||| A token representing the world, for use in `IO`
abstract data World = TheWorld prim__WorldType

private
world : World -> prim__WorldType
world (TheWorld w) = w

abstract WorldRes : Type -> Type
WorldRes x = x

record FFI where
  ffi_types : Type -> Type
  ffi_fn : Type
  constructor MkFFI
{-
record FFI : Type where
     MkFFI : (ffi_types : Type -> Type) -> (ffi_fn : Type) -> FFI
-}
abstract 
data IO' : (lang : FFI) -> Type -> Type where
     MkIO : (World -> PrimIO (WorldRes a)) -> IO' lang a

data FTy : FFI -> List Type -> Type -> Type where
     FRet : ffi_types f t -> FTy f xs (IO' f t)
     FFun : ffi_types f s -> FTy f (s :: xs) t -> FTy f xs (s -> t)

namespace ForeignEnv
  data FEnv : FFI -> List Type -> Type where
       Nil : FEnv f []
       (::) : (ffi_types f t, t) -> FEnv f xs -> FEnv f (t :: xs)
  
ForeignPrimType : (xs : List Type) -> FEnv ffi xs -> Type -> Type
ForeignPrimType {ffi} [] [] t = World -> ffi_fn ffi -> ffi_types ffi t -> PrimIO t
ForeignPrimType {ffi} (x :: xs) ((a, _) :: env) t 
     = (ffi_types ffi x, x) -> ForeignPrimType xs env t

%inline
applyEnv : (env : FEnv ffi xs) -> 
           ForeignPrimType xs env t -> 
           World -> ffi_fn ffi -> ffi_types ffi t -> PrimIO t
applyEnv [] f = f
applyEnv (x@(_, _) :: xs) f = applyEnv xs (f x)

mkForeignPrim : ForeignPrimType xs env t
-- compiled as primitive

%inline
foreign_prim : (f : FFI) -> 
               (fname : ffi_fn f) -> FTy f xs ty -> FEnv f xs -> ty
foreign_prim f fname (FRet y) env
        = MkIO (\w => applyEnv env mkForeignPrim w fname y)
foreign_prim f fname (FFun arg sc) env
        = \x => foreign_prim f fname sc ((arg, x) :: env)

%inline
foreign : (f : FFI) -> (fname : ffi_fn f) -> (ty : Type) ->
          {auto fty : FTy f [] ty} -> ty
foreign ffi fname ty {fty} = foreign_prim ffi fname fty []

abstract
prim_io_bind : PrimIO a -> (a -> PrimIO b) -> PrimIO b
prim_io_bind (prim__IO v) k = k v

unsafePerformPrimIO : PrimIO a -> a
-- compiled as primitive

abstract
prim_io_return : a -> PrimIO a
prim_io_return x = prim__IO x

abstract
io_bind : IO' l a -> (a -> IO' l b) -> IO' l b
io_bind (MkIO fn) k
   = MkIO (\w => prim_io_bind (fn w)
                    (\ b => case k b of
                                 MkIO fkb => fkb w))

abstract
io_return : a -> IO' l a
io_return x = MkIO (\w => prim_io_return x)

liftPrimIO : (World -> PrimIO a) -> IO' l a
liftPrimIO = MkIO

run__IO : IO' l () -> PrimIO ()
run__IO (MkIO f) = f (TheWorld prim__TheWorld)

unsafePerformIO : IO' ffi a -> a
unsafePerformIO (MkIO f) = unsafePerformPrimIO
        (prim_io_bind (f (TheWorld prim__TheWorld)) (\ b => prim_io_return b))

prim_read : IO' l String
prim_read = MkIO (\w => prim_io_return (prim__readString (world w)))

prim_write : String -> IO' l Int
prim_write s 
   = MkIO (\w => prim_io_return (prim__writeString (world w) s))

prim_fread : Ptr -> IO' l String
prim_fread h = MkIO (\w => prim_io_return (prim__readFile (world w) h))

prim_fwrite : Ptr -> String -> IO' l Int
prim_fwrite h s 
   = MkIO (\w => prim_io_return (prim__writeFile (world w) h s))

--------- The C FFI

data Raw : Type -> Type where
     -- code generated can assume it's compiled just as 't'
     MkRaw : (x : t) -> Raw t

-- Tell erasure analysis not to erase the argument
%used MkRaw x

-- Supported C integer types
data C_IntTypes : Type -> Type where
     C_IntChar   : C_IntTypes Char
     C_IntNative : C_IntTypes Int
     C_IntBits8  : C_IntTypes Bits8
     C_IntBits16 : C_IntTypes Bits16
     C_IntBits32 : C_IntTypes Bits32
     C_IntBits64 : C_IntTypes Bits64
     C_IntB8x16  : C_IntTypes Bits8x16
     C_IntB16x8  : C_IntTypes Bits16x8
     C_IntB32x4  : C_IntTypes Bits32x4
     C_IntB64x2  : C_IntTypes Bits64x2

-- Supported C foreign types
data C_Types : Type -> Type where
     C_Str   : C_Types String
     C_Float : C_Types Float
     C_Ptr   : C_Types Ptr
     C_MPtr  : C_Types ManagedPtr
     C_Unit  : C_Types ()
     C_Any   : C_Types (Raw a)
     C_IntT  : C_IntTypes i -> C_Types i

FFI_C : FFI                                     
FFI_C = MkFFI C_Types String

IO : Type -> Type
IO = IO' FFI_C

run__provider : IO a -> PrimIO a
run__provider (MkIO f) = f (TheWorld prim__TheWorld)

prim_fork : PrimIO () -> PrimIO Ptr
prim_fork x = prim_io_return prim__vm -- compiled specially

fork : IO () -> IO Ptr
fork (MkIO f) = MkIO (\w => prim_io_bind
                              (prim_fork (prim_io_bind (f w)
                                   (\ x => prim_io_return x)))
                              (\x => prim_io_return x))

forceGC : IO ()
forceGC = foreign FFI_C "idris_forceGC" (Ptr -> IO ()) prim__vm

--------- The Javascript/Node FFI


-- Supported JS foreign types
mutual
  data JsFn : Type -> Type where
       MkJsFn : (x : t) -> JsFn t

  data JS_IntTypes  : Type -> Type where
       JS_IntChar   : JS_IntTypes Char
       JS_IntNative : JS_IntTypes Int

  data JS_FnTypes : Type -> Type where
       JS_Fn     : JS_Types s -> JS_FnTypes t -> JS_FnTypes (s -> t)
       JS_FnIO   : JS_Types t -> JS_FnTypes (IO' l t)
       JS_FnBase : JS_Types t -> JS_FnTypes t

  data JS_Types : Type -> Type where
       JS_Str   : JS_Types String
       JS_Float : JS_Types Float
       JS_Ptr   : JS_Types Ptr
       JS_Unit  : JS_Types ()
       JS_FnT   : JS_FnTypes a -> JS_Types (JsFn a)
       JS_IntT  : JS_IntTypes i -> JS_Types i

-- Tell erasure analysis not to erase the argument. Needs to be outside the
-- mutual block, since directives are done on the first pass and in the first
-- pass we only have 'JsFn' and not the constructor.
%used MkJsFn x

FFI_JS : FFI                                     
FFI_JS = MkFFI JS_Types String

JS_IO : Type -> Type
JS_IO = IO' FFI_JS

