import list;

data IO a = prim__IO a;

io_bind : IO a -> (a -> IO b) -> IO b;
io_bind (prim__IO v) k = k v;

io_return : a -> IO a;
io_return = prim__IO;

data FTy = FInt | FFloat | FChar | FString | FPtr | FUnit;

interpFTy : FTy -> Set;
interpFTy FInt    = Int;
interpFTy FFloat  = Float;
interpFTy FChar   = Char;
interpFTy FString = String;
interpFTy FPtr    = Ptr;
interpFTy FUnit   = ();

ForeignTy : (xs:List FTy) -> (t:FTy) -> Set;
ForeignTy xs t = mkForeign (rev xs) (IO (interpFTy t)) where {
   mkForeign : List FTy -> Set -> Set;
   mkForeign Nil ty         = ty;
   mkForeign (Cons s ss) ty = mkForeign ss (interpFTy s -> ty);
}

data FEnv : List FTy -> Set where
    FEmpty : FEnv Nil
  | FCons  : {xs:List FTy} ->
             interpFTy x -> FEnv xs -> FEnv (Cons x xs);

data Foreign : Set -> Set where
    FFun : String -> (xs:List FTy) -> (t:FTy) -> 
           Foreign (ForeignTy xs t);

mkForeign : Foreign x -> x;
-- mkForeign compiled as primitive

