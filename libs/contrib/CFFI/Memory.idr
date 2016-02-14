||| Machinery for interfacing with C.
module CFFI.Memory

import CFFI.Types
import Data.Vect
import Data.HVect

%include C "memory.h"

%access public export
%default partial

data CPtr = CPt Ptr Int CType

implicit decayCPtr : CPtr -> Ptr
decayCPtr (CPt p _ _) = p

Show CPtr where
    show (CPt _ os t) = "CPtr ptr " ++ show os ++ " " ++ show t

malloc : Int -> IO Ptr
malloc size = foreign FFI_C "malloc" (Int -> IO Ptr) size

mfree : Ptr -> IO ()
mfree ptr = foreign FFI_C "free" (Ptr -> IO ()) ptr

alloc : CType -> IO CPtr
alloc t = return $ CPt !(malloc (sizeOf t)) 0 t

free : CPtr -> IO ()
free (CPt p _ _) = mfree p

withAlloc : CType -> (CPtr -> IO ()) -> IO ()
withAlloc t f = do m <- alloc t
                   f m
                   free m

infixl 1 ~~>

(~~>) :  CType -> (CPtr -> IO ()) -> IO ()
(~~>) = withAlloc

ctype : CPtr -> CType
ctype (CPt _ _ t) = t
mutual
    -- peekArray : (c : CPtr) -> IO (translate (ctype c))
    -- peekArray (CPt p o a@(ARRAY n t)) = do
    --     os <- return $ fromList (offsets a)
    --     map (\x => peek (CPt p x t)) os

    -- pokeArray : (c : CPtr) -> translate (ctype c) -> IO ()
    -- pokeArray (CPt p o a@(ARRAY n t)) x = do
    --            os <- fromList $ offsets a
    --            ox <- zip os x
    --            map (\(x, y)=>poke (CPt p x t) y) ox
    --            return ()

    peek : (p : CPtr) -> IO (translate (ctype p))
    peek (CPt p o I8) = prim_peek8 p o
    peek (CPt p o I16) = prim_peek16 p o
    peek (CPt p o I32) = prim_peek32 p o
    peek (CPt p o I64) = prim_peek64 p o
    peek (CPt p o FLOAT) = prim_peekSingle p o
    peek (CPt p o DOUBLE) = prim_peekDouble p o
    peek (CPt p o PTR) = prim_peekPtr p o
    -- peek cp@(CPt p o (ARRAY n t)) = peekArray cp
    -- peek (CPt p o (UNION xs)) = ?peekUnion
    -- peek (CPt p o (STRUCT xs)) = ?peekStruct
    -- peek (CPt p o (PACKEDSTRUCT xs)) = ?peekPacked


    poke : (p : CPtr) -> translate $ ctype p -> IO ()
    poke (CPt p o I8) x = do _ <- prim_poke8 p o x
                             return ()
    poke (CPt p o I16) x = do _ <- prim_poke16 p o x
                              return ()
    poke (CPt p o I32) x = do _ <- prim_poke32 p o x
                              return ()
    poke (CPt p o I64) x = do _ <- prim_poke64 p o x
                              return ()
    poke (CPt p o PTR) x = do _ <- prim_pokePtr p o x
                              return ()
    poke (CPt p o FLOAT) x = do _ <- prim_pokeSingle p o x
                                return ()
    poke (CPt p o DOUBLE) x = do _ <- prim_pokeDouble p o x
                                 return ()
    -- poke cp@(CPt p o (ARRAY n t)) x = pokeArray cp x
    -- poke (CPt p o (UNION xs)) x = ?pokeUnion
    -- poke (CPt p o (STRUCT xs)) x = ?pokeStruct
    -- poke (CPt p o (PACKEDSTRUCT xs)) x = ?pokePacked

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
