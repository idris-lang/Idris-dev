%unqualified

import Builtins
import Prelude.List

%access public

||| Idris's primitive IO, for building abstractions on top of
abstract
data PrimIO : Type -> Type where
     Prim__IO : a -> PrimIO a

||| A token representing the world, for use in `IO`
abstract data World = TheWorld prim__WorldType

private
world : World -> prim__WorldType
world (TheWorld w) = w

abstract WorldRes : Type -> Type
WorldRes x = x

||| An FFI specifier, which describes how a particular compiler
||| backend handles foreign function calls.
record FFI where
  constructor MkFFI
  ||| A family describing which types are available in the FFI
  ffi_types : Type -> Type

  ||| The type used to specify the names of foreign functions in this FFI
  ffi_fn : Type

  ||| How this FFI describes exported datatypes
  ffi_data : Type

||| The IO type, parameterised over the FFI that is available within
||| it.
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

mkForeignPrim : {xs : _} -> {ffi : _} -> {env : FEnv ffi xs} -> {t : Type} ->
                ForeignPrimType xs env t
-- compiled as primitive. Compiler assumes argument order, so make it
-- explicit here.

%inline
foreign_prim : (f : FFI) -> 
               (fname : ffi_fn f) -> FTy f xs ty -> FEnv f xs -> ty
foreign_prim f fname (FRet y) env
        = MkIO (\w => applyEnv env mkForeignPrim w fname y)
foreign_prim f fname (FFun arg sc) env
        = \x => foreign_prim f fname sc ((arg, x) :: env)

||| Call a foreign function.
|||
||| The particular semantics of foreign function calls depend on the
||| Idris compiler backend in use. For the default C backend, see the
||| documentation for `FFI_C`.
|||
||| For more details, please consult [the Idris documentation](http://docs.idris-lang.org/en/latest/reference/ffi.html).
|||
||| @ f     an FFI descriptor, which is specific to the compiler backend.
||| @ fname the name of the foreign function
||| @ ty    the Idris type for the foreign function
||| @ fty   an automatically-found proof that the Idris type works with
|||         the FFI in question
%inline
foreign : (f : FFI) -> (fname : ffi_fn f) -> (ty : Type) ->
          {auto fty : FTy f [] ty} -> ty
foreign ffi fname ty {fty} = foreign_prim ffi fname fty []

abstract
prim_io_bind : PrimIO a -> (a -> PrimIO b) -> PrimIO b
prim_io_bind (Prim__IO v) k = k v

unsafePerformPrimIO : PrimIO a -> a
-- compiled as primitive

abstract
prim_io_return : a -> PrimIO a
prim_io_return x = Prim__IO x

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

call__IO : IO' ffi a -> PrimIO a
call__IO (MkIO f) = f (TheWorld prim__TheWorld)

-- Concrete type makes it easier to elaborate at top level
run__IO : IO' ffi () -> PrimIO ()
run__IO f = call__IO f

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
namespace FFI_C
  data Raw : Type -> Type where
       -- code generated can assume it's compiled just as 't'
       MkRaw : (x : t) -> Raw t

  -- Tell erasure analysis not to erase the argument
  %used MkRaw x

  ||| Supported C integer types
  data C_IntTypes : Type -> Type where
       C_IntChar   : C_IntTypes Char
       C_IntNative : C_IntTypes Int
       C_IntBits8  : C_IntTypes Bits8
       C_IntBits16 : C_IntTypes Bits16
       C_IntBits32 : C_IntTypes Bits32
       C_IntBits64 : C_IntTypes Bits64

  ||| Supported C foreign types
  data C_Types : Type -> Type where
       C_Str   : C_Types String
       C_Float : C_Types Float
       C_Ptr   : C_Types Ptr
       C_MPtr  : C_Types ManagedPtr
       C_Unit  : C_Types ()
       C_Any   : C_Types (Raw a)
       C_IntT  : C_IntTypes i -> C_Types i

  ||| A descriptor for the C FFI. See the constructors of `C_Types`
  ||| and `C_IntTypes` for the concrete types that are available.
  %error_reverse
  FFI_C : FFI
  FFI_C = MkFFI C_Types String String

||| The type of interactive programs, performing some I/O side effects
||| and returning a value.
||| @res The result type of the program 
%error_reverse
IO : (res : Type) -> Type
IO = IO' FFI_C

-- Cannot be relaxed as is used by type providers and they expect IO a
-- in the first argument.
run__provider : IO a -> PrimIO a
run__provider (MkIO f) = f (TheWorld prim__TheWorld)

prim_fork : PrimIO () -> PrimIO Ptr
prim_fork x = prim_io_return prim__vm -- compiled specially

namespace IO
  fork : IO' l () -> IO' l Ptr
  fork (MkIO f) = MkIO (\w => prim_io_bind
                                (prim_fork (prim_io_bind (f w)
                                     (\ x => prim_io_return x)))
                                (\x => prim_io_return x))

  forceGC : IO ()
  forceGC = foreign FFI_C "idris_forceGC" (Ptr -> IO ()) prim__vm

  getErrno : IO Int
  getErrno = foreign FFI_C "idris_errno" (IO Int)

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

||| The JavaScript FFI. The strings naming functions in this API are
||| JavaScript code snippets, into which the arguments are substituted
||| for the placeholders `%0`, `%1`, etc.
%error_reverse
FFI_JS : FFI
FFI_JS = MkFFI JS_Types String String

%error_reverse
JS_IO : Type -> Type
JS_IO = IO' FFI_JS


--------- Foreign Exports

namespace FFI_Export
-- It's just like Data.List.Elem, but we don't need all the other stuff
-- that comes with it, just a proof that a data type is defined.
  data DataDefined : Type -> List (Type, s) -> s -> Type where
       DHere : DataDefined x ((x, t) :: xs) t
       DThere : DataDefined x xs t -> DataDefined x (y :: xs) t

  data FFI_Base : (f : FFI) -> List (Type, ffi_data f) -> Type -> Type where
       FFI_ExpType : {n : ffi_data f} -> (def : DataDefined t xs n) -> FFI_Base f xs t
       FFI_Prim : (prim : ffi_types f t) -> FFI_Base f xs t

  %used FFI_ExpType n
  %used FFI_ExpType def
  %used FFI_Prim prim

  data FFI_Exportable : (f : FFI) -> List (Type, ffi_data f) -> Type -> Type where
       FFI_IO : (b : FFI_Base f xs t) -> FFI_Exportable f xs (IO' f t)
       FFI_Fun : (b : FFI_Base f xs s) -> (a : FFI_Exportable f xs t) -> FFI_Exportable f xs (s -> t)
       FFI_Ret : (b : FFI_Base f xs t) -> FFI_Exportable f xs t

  %used FFI_IO b
  %used FFI_Fun b
  %used FFI_Fun a
  %used FFI_Ret b

  data FFI_Export : (f : FFI) -> String -> List (Type, ffi_data f) -> Type where
       Data : (x : Type) -> (n : ffi_data f) -> 
              (es : FFI_Export f h ((x, n) :: xs)) -> FFI_Export f h xs
       Fun : (fn : t) -> (n : ffi_fn f) -> {auto prf : FFI_Exportable f xs t} -> 
             (es : FFI_Export f h xs) -> FFI_Export f h xs
       End : FFI_Export f h xs

%used Data x
%used Data n
%used Data es
%used Fun fn
%used Fun n
%used Fun es
%used Fun prf

