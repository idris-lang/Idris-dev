%unqualified

import Prelude.List

%access public

abstract data PrimIO a = prim__IO a

abstract data World = TheWorld

abstract WorldRes : Type -> Type
WorldRes x = x

-- abstract data WorldRes a = MkWR a World

abstract data IO a = MkIO (World -> PrimIO (WorldRes a))

abstract
prim_io_bind : PrimIO a -> (a -> PrimIO b) -> PrimIO b
prim_io_bind (prim__IO v) k = k v

unsafePerformPrimIO : PrimIO a -> a
-- compiled as primitive

abstract
prim_io_return : a -> PrimIO a
prim_io_return x = prim__IO x

data IntTy = ITChar | ITNative | IT8 | IT16 | IT32 | IT64 | IT8x16 | IT16x8 | IT32x4 | IT64x2
data FTy = FIntT IntTy
         | FFunction FTy FTy
         | FFloat
         | FString
         | FPtr
         | FAny Type
         | FUnit

FInt : FTy
FInt = FIntT ITNative

FChar : FTy
FChar = FIntT ITChar

FByte : FTy
FByte = FIntT IT8

FShort : FTy
FShort = FIntT IT16

FLong : FTy
FLong = FIntT IT64

FBits8 : FTy
FBits8 = FIntT IT8

FBits16 : FTy
FBits16 = FIntT IT16

FBits32 : FTy
FBits32 = FIntT IT32

FBits64 : FTy
FBits64 = FIntT IT64

FBits8x16 : FTy
FBits8x16 = FIntT IT8x16

FBits16x8 : FTy
FBits16x8 = FIntT IT16x8

FBits32x4 : FTy
FBits32x4 = FIntT IT32x4

FBits64x2 : FTy
FBits64x2 = FIntT IT64x2

interpFTy : FTy -> Type
interpFTy (FIntT ITNative) = Int
interpFTy (FIntT ITChar)   = Char
interpFTy (FIntT IT8)      = Bits8
interpFTy (FIntT IT16)     = Bits16
interpFTy (FIntT IT32)     = Bits32
interpFTy (FIntT IT64)     = Bits64
interpFTy (FAny t)         = t
interpFTy FFloat           = Float
interpFTy FString          = String
interpFTy FPtr             = Ptr
interpFTy (FIntT IT8x16)   = Bits8x16
interpFTy (FIntT IT16x8)   = Bits16x8
interpFTy (FIntT IT32x4)   = Bits32x4
interpFTy (FIntT IT64x2)   = Bits64x2
interpFTy FUnit            = ()

interpFTy (FFunction a b) = interpFTy a -> interpFTy b

ForeignTy : (xs:List FTy) -> (t:FTy) -> Type
ForeignTy Nil     rt = World -> PrimIO (interpFTy rt)
ForeignTy (t::ts) rt = interpFTy t -> ForeignTy ts rt


data Foreign : Type -> Type where
    FFun : String -> (xs:List FTy) -> (t:FTy) ->
           Foreign (ForeignTy xs t)

mkForeignPrim : Foreign x -> x
mkLazyForeignPrim : Foreign x -> x
-- mkForeign and mkLazyForeign compiled as primitives

abstract
io_bind : IO a -> (a -> IO b) -> IO b
io_bind (MkIO fn) k
   = MkIO (\w => prim_io_bind (fn w)
                    (\ b => case k b of
                                 MkIO fkb => fkb w))

abstract
io_return : a -> IO a
io_return x = MkIO (\w => prim_io_return x)

liftPrimIO : (World -> PrimIO a) -> IO a
liftPrimIO f = MkIO (\w => prim_io_bind (f w)
                         (\x => prim_io_return x))

run__IO : IO () -> PrimIO ()
run__IO (MkIO f) = prim_io_bind (f TheWorld)
                        (\ b => prim_io_return b)

run__provider : IO a -> PrimIO a
run__provider (MkIO f) = prim_io_bind (f TheWorld)
                            (\ b => prim_io_return b)

-- io_bind v (\v' => io_return v')

prim_fork : |(thread:PrimIO ()) -> PrimIO Ptr
prim_fork x = prim_io_return prim__vm -- compiled specially

fork : |(thread:IO ()) -> IO Ptr
fork (MkIO f) = MkIO (\w => prim_io_bind
                              (prim_fork (prim_io_bind (f w)
                                   (\ x => prim_io_return x)))
                              (\x => prim_io_return x))

partial
prim_fread : Ptr -> IO String
prim_fread h = MkIO (\w => prim_io_return (prim__readString h))

unsafePerformIO : IO a -> a
unsafePerformIO (MkIO f) = unsafePerformPrimIO
        (prim_io_bind (f TheWorld) (\ b => prim_io_return b))


