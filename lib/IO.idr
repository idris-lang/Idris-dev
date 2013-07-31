import Prelude.List

%access public

abstract data UnsafeIO a = prim__IO a

abstract
io_bind : UnsafeIO a -> (a -> UnsafeIO b) -> UnsafeIO b
io_bind (prim__IO v) k = k v

unsafePerformIO : UnsafeIO a -> a
-- compiled as primitive

abstract
io_return : a -> UnsafeIO a
io_return x = prim__IO x

-- This may seem pointless, but we can use it to force an
-- evaluation of main that Epic wouldn't otherwise do...

run__IO : UnsafeIO () -> UnsafeIO ()
run__IO v = io_bind v (\v' => io_return v')

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
ForeignTy Nil     rt = UnsafeIO (interpFTy rt)
ForeignTy (t::ts) rt = interpFTy t -> ForeignTy ts rt


data Foreign : Type -> Type where
    FFun : String -> (xs:List FTy) -> (t:FTy) -> 
           Foreign (ForeignTy xs t)

mkForeign : Foreign x -> x
mkLazyForeign : Foreign x -> x
-- mkForeign and mkLazyForeign compiled as primitives

fork : |(thread:UnsafeIO ()) -> UnsafeIO Ptr
fork x = io_return prim__vm -- compiled specially


