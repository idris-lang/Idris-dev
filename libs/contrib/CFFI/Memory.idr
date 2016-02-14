||| Machinery for interfacing with C.
module CFFI.Memory

import CFFI.Types
import Data.Vect
import Data.HVect

%include C "memory.h"

%access public export
%default partial

data CPtr = CPt Ptr Int Composite

implicit decayCPtr : CPtr -> Ptr
decayCPtr (CPt p _ _) = p

Show CPtr where
    show (CPt _ os t) = "CPtr ptr " ++ show os ++ " " ++ show t

malloc : Int -> IO Ptr
malloc size = foreign FFI_C "malloc" (Int -> IO Ptr) size

mfree : Ptr -> IO ()
mfree ptr = foreign FFI_C "free" (Ptr -> IO ()) ptr

alloc : Composite -> IO CPtr
alloc t = return $ CPt !(malloc (sizeOfComp t)) 0 t

free : CPtr -> IO ()
free (CPt p _ _) = mfree p

withAlloc : Composite -> (CPtr -> IO ()) -> IO ()
withAlloc t f = do m <- alloc t
                   f m
                   free m

infixl 1 ~~>

(~~>) :  Composite-> (CPtr -> IO ()) -> IO ()
(~~>) = withAlloc

ctype : CPtr -> CType
ctype (CPt _ _ (T t)) = t

mutual
{-
    peekArray : (c : CPtr) -> IO (translate (ctype c))
    peekArray (CPt p o a@(ARRAY n t)) = do
        os <- return $ fromList (offsets a)
        traverse (\x => peek (CPt p x t)) os

    pokeArray : (c : CPtr) -> translate (ctype c) -> IO ()
    pokeArray (CPt p o a@(ARRAY n t)) x = do
        os <- fromList $ offsets a
        ox <- zip os x
        traverse_ (\(x, y)=>poke (CPt p x t) y) ox
-}
    peek : (p : CPtr) -> (t: CType) -> IO (translate t)
    peek (CPt p o (T I8)) I8 = prim_peek8 p o
    peek (CPt p o (T I16)) I16= prim_peek16 p o
    peek (CPt p o (T I32)) I32 = prim_peek32 p o
    peek (CPt p o (T I64)) I64 = prim_peek64 p o
    peek (CPt p o (T FLOAT)) FLOAT = prim_peekSingle p o
    peek (CPt p o (T DOUBLE)) DOUBLE = prim_peekDouble p o
    peek (CPt p o (T PTR)) PTR = prim_peekPtr p o
    -- peek cp@(CPt p o (ARRAY n t)) = peekArray cp
    -- peek (CPt p o (UNION xs)) = ?peekUnion
    -- peek (CPt p o (STRUCT xs)) = ?peekStruct
    -- peek (CPt p o (PACKEDSTRUCT xs)) = ?peekPacked


    poke : (p : CPtr) -> (t : CType) -> translate t -> IO ()
    poke (CPt p o (T I8)) I8 x = do _ <- prim_poke8 p o x
                                    return ()
    poke (CPt p o (T I16)) I16 x = do _ <- prim_poke16 p o x
                                      return ()
    poke (CPt p o (T I32)) I32 x = do _ <- prim_poke32 p o x
                                      return ()
    poke (CPt p o (T I64)) I64 x = do _ <- prim_poke64 p o x
                                      return ()
    poke (CPt p o (T PTR)) PTR x = do _ <- prim_pokePtr p o x
                                      return ()
    poke (CPt p o (T FLOAT)) FLOAT x = do _ <- prim_pokeSingle p o x
                                          return ()
    poke (CPt p o (T DOUBLE)) DOUBLE x = do _ <- prim_pokeDouble p o x
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
