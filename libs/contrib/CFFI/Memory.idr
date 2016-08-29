||| Machinery for interfacing with C.
module CFFI.Memory

import CFFI.Types
import Data.Vect

%include C "memory.h"

%access public export
%default partial


data CPtr = CPt Ptr Int

implicit toCPtr : Ptr -> CPtr
toCPtr p = CPt p 0

implicit toPtr : CPtr -> Ptr
toPtr (CPt p 0) = p
toPtr (CPt p o) = prim__ptrOffset p o

||| Import of calloc from the C standard library.
calloc : Int -> Int -> IO Ptr
calloc nmemb size = foreign FFI_C "calloc" (Int -> Int -> IO Ptr) nmemb size

||| Import of malloc from the C standard library.
malloc : Int -> IO Ptr
malloc size = foreign FFI_C "malloc" (Int -> IO Ptr) size

||| Import of free from the C standard library.
mfree : Ptr -> IO ()
mfree ptr = foreign FFI_C "free" (Ptr -> IO ()) ptr

||| Allocate enough memory to hold an instance of a C typr
alloc : Composite -> IO CPtr
alloc t = pure $ CPt !(calloc 1 (sizeOf t)) 0

||| Free memory allocated with alloc
free : CPtr -> IO ()
free (CPt p _ ) = mfree p

||| Perform an IO action with memory that is freed afterwards
withAlloc : Composite -> (CPtr -> IO ()) -> IO ()
withAlloc t f = do m <- alloc t
                   f m
                   free m

infixl 1 ~~>
||| Perform an IO action with memory that is freed afterwards
(~~>) :  Composite-> (CPtr -> IO ()) -> IO ()
(~~>) = withAlloc

||| Read from memory
peek : (t: CType) -> CPtr -> IO (translate t)
peek I8 (CPt p o) = prim_peek8 p o
peek I16 (CPt p o) = prim_peek16 p o
peek I32 (CPt p o) = prim_peek32 p o
peek I64 (CPt p o) = prim_peek64 p o
peek FLOAT (CPt p o) = prim_peekSingle p o
peek DOUBLE (CPt p o) = prim_peekDouble p o
peek PTR (CPt p o) = prim_peekPtr p o

||| Write to memory
poke : (t : CType) -> CPtr -> translate t -> IO ()
poke I8 (CPt p o) x = do _ <- prim_poke8 p o x
                         pure ()
poke I16 (CPt p o) x = do _ <- prim_poke16 p o x
                          pure ()
poke I32 (CPt p o) x = do _ <- prim_poke32 p o x
                          pure ()
poke I64 (CPt p o) x = do _ <- prim_poke64 p o x
                          pure ()
poke PTR (CPt p o) x = do _ <- prim_pokePtr p o x
                          pure ()
poke FLOAT (CPt p o) x = do _ <- prim_pokeSingle p o x
                            pure ()
poke DOUBLE (CPt p o) x = do _ <- prim_pokeDouble p o x
                             pure ()

||| Update memory with a function.
update : (t: CType) -> CPtr -> (translate t -> translate t) -> IO ()
update ty cp f = do val <- peek ty cp
                    out <- pure $ f val
                    poke ty cp out

||| Get a pointer to a field in a composite value
field : Composite -> Nat ->  CPtr -> CPtr
field arr@(ARRAY n t) i (CPt p o) = CPt p (o + offset arr i)
field un@(UNION xs) i (CPt p o) = CPt p o
field st@(STRUCT xs) i (CPt p o) = CPt p (o + offset st i)
field ps@(PACKEDSTRUCT xs) i (CPt p o) = CPt p (o + offset ps i)
field (T t) Z p = p

infixl 10 #

||| Get a pointer to a field in a composite value
(#) : Composite -> Nat -> CPtr -> CPtr
(#) = field
