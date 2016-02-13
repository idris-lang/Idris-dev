||| Machinery for interfacing with C.
module CFFI.Memory

import CFFI.Types

%include C "memory.h"

%access public export
%default partial

data CPtr = CPt Ptr Int CType

malloc : Int -> IO Ptr
malloc size = foreign FFI_C "malloc" (Int -> IO Ptr) size

mfree : Ptr -> IO ()
mfree ptr = foreign FFI_C "free" (Ptr -> IO ()) ptr

alloc : CType -> IO CPtr
alloc t = return $ CPt !(malloc (sizeOf t)) 0 t

free : CPtr -> IO ()
free (CPt p _ _) = mfree p

ctype : CPtr -> CType
ctype (CPt _ _ t) = t


get : (p : CPtr) -> IO (translate (ctype p))
get (CPt p o I8) = prim_peek8 p o
get (CPt p o I16) = prim_peek16 p o
get (CPt p o I32) = prim_peek32 p o
get (CPt p o I64) = prim_peek64 p o
get (CPt p o FLOAT) = prim_peekSingle p o
get (CPt p o DOUBLE) = prim_peekDouble p o
get (CPt p o PTR) = prim_peekPtr p o
get (CPt p o (ARRAY n t)) = ?getArray
get (CPt p o (UNION xs)) = ?getUnion
get (CPt p o (STRUCT xs)) = ?getStruct
get (CPt p o (PACKEDSTRUCT xs)) = ?getPacked


put : (p : CPtr) -> (translate (ctype p)) -> IO ()
put (CPt p o I8) x = do _ <- prim_poke8 p o x
                        return ()
put (CPt p o I16) x = do _ <- prim_poke16 p o x
                         return ()
put (CPt p o I32) x = do _ <- prim_poke32 p o x
                         return ()
put (CPt p o I64) x = do _ <- prim_poke64 p o x
                         return ()
put (CPt p o PTR) x = do _ <- prim_pokePtr p o x
                         return ()
put (CPt p o FLOAT) x = do _ <- prim_pokeSingle p o x
                           return ()
put (CPt p o DOUBLE) x = do _ <- prim_pokeDouble p o x
                            return ()
put (CPt p o (ARRAY n t)) x = ?putArray
put (CPt p o (UNION xs)) x = ?putUnion
put (CPt p o (STRUCT xs)) x = ?putStruct
put (CPt p o (PACKEDSTRUCT xs)) x = ?putPacked

-- update : (p : CPtr) -> ((translate(ctype p)) -> (translate (ctype p)) -> IO ()
-- TODO : Fix bounds checking
field : CPtr -> Nat ->  CPtr
field (CPt p o arr@(ARRAY n t)) i = CPt p (o + offset arr i) t
field (CPt p o un@(UNION xs)) i = CPt p o (select un i)
field (CPt p o st@(STRUCT xs)) i = CPt p (o + offset st i) (select st i)
field (CPt p o ps@(PACKEDSTRUCT xs)) i = CPt p (o + offset ps i) (select ps i)
field p Z = p

infixl 10 #

(#) : CPtr -> Nat -> CPtr
(#) = field
