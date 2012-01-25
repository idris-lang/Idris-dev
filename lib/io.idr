import prelude.list

%access public

abstract data IO a = prim__IO a

abstract
io_bind : IO a -> (a -> IO b) -> IO b
io_bind (prim__IO v) k = k v

abstract
io_return : a -> IO a
io_return x = prim__IO x

-- This may seem pointless, but we can use it to force an
-- evaluation of main that Epic wouldn't otherwise do...

run__IO : IO () -> IO ()
run__IO v = io_bind v (\v' => io_return v')

data FTy = FInt | FFloat | FChar | FString | FPtr | FUnit

interpFTy : FTy -> Set
interpFTy FInt    = Int
interpFTy FFloat  = Float
interpFTy FChar   = Char
interpFTy FString = String
interpFTy FPtr    = Ptr
interpFTy FUnit   = ()

ForeignTy : (xs:List FTy) -> (t:FTy) -> Set
ForeignTy xs t = mkForeign' (reverse xs) (IO (interpFTy t)) where 
   mkForeign' : List FTy -> Set -> Set
   mkForeign' Nil ty       = ty
   mkForeign' (s :: ss) ty = mkForeign' ss (interpFTy s -> ty)


data Foreign : Set -> Set where
    FFun : String -> (xs:List FTy) -> (t:FTy) -> 
           Foreign (ForeignTy xs t)

mkForeign : Foreign x -> x
-- mkForeign compiled as primitive


