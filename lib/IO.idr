import Prelude.List

%access public

abstract data IO a = prim__IO a

abstract
io_bind : IO a -> (a -> IO b) -> IO b
io_bind (prim__IO v) k = k v

unsafePerformIO : IO a -> a
-- compiled as primitive

abstract
io_return : a -> IO a
io_return x = prim__IO x

-- This may seem pointless, but we can use it to force an
-- evaluation of main that Epic wouldn't otherwise do...

run__IO : IO () -> IO ()
run__IO v = io_bind v (\v' => io_return v')

data IntTy = ITNative | IT8 | IT16 | IT32 | IT64
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
FChar = FIntT IT8

FShort : FTy
FShort = FIntT IT16

FLong : FTy
FLong = FIntT IT64

interpFTy : FTy -> Type
interpFTy (FIntT ITNative) = Int
interpFTy (FIntT IT8)      = Bits8
interpFTy (FIntT IT16)     = Bits16
interpFTy (FIntT IT32)     = Bits32
interpFTy (FIntT IT64)     = Bits64
interpFTy (FAny t)         = t
interpFTy FFloat           = Float
interpFTy FString          = String
interpFTy FPtr             = Ptr
interpFTy FUnit            = ()

interpFTy (FFunction a b) = interpFTy a -> interpFTy b

ForeignTy : (xs:List FTy) -> (t:FTy) -> Type
ForeignTy Nil     rt = IO (interpFTy rt)
ForeignTy (t::ts) rt = interpFTy t -> ForeignTy ts rt


data Foreign : Type -> Type where
    FFun : String -> (xs:List FTy) -> (t:FTy) -> 
           Foreign (ForeignTy xs t)

mkForeign : Foreign x -> x
mkLazyForeign : Foreign x -> x
-- mkForeign and mkLazyForeign compiled as primitives

fork : |(thread:IO ()) -> IO Ptr
fork x = io_return prim__vm -- compiled specially


