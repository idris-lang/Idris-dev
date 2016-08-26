module Data.ByteArray

%include C "array.h"
%link C "array.o"

%access public export
%default total

namespace Byte
  Byte : Type
  Byte = Bits8

  toInt : Byte -> Int
  toInt = prim__zextB8_Int

  fromInt : Int -> Byte
  fromInt = prim__truncInt_B8

export
record ByteArray where
  constructor BA
  ptr : CData
  sz : Int

-- This needn't be precise; it just needs to be enough to be safe.
export
bytesPerInt : Int
bytesPerInt = 8

export
allocate : Int -> IO ByteArray
allocate sz = do
  ptr <- foreign FFI_C "array_alloc" (Int -> IO CData) sz
  pure $ BA ptr sz

export
reallocate : Int -> ByteArray -> IO ()
reallocate newSz (BA ptr sz)
  = foreign FFI_C "array_realloc" (Int -> CData -> IO ()) sz ptr

export
peek : Int -> ByteArray -> IO Byte
peek ofs (BA ptr sz)
  = if (ofs < 0 || ofs >= sz)
      then pure 0
      else foreign FFI_C "array_peek" (Int -> CData -> IO Byte) ofs ptr

export
peekInt : Int -> ByteArray -> IO Int
peekInt ofs (BA ptr sz)
  = if (ofs < 0 || ofs+bytesPerInt > sz)
      then pure 0
      else foreign FFI_C "array_peek_int" (Int -> CData -> IO Int) ofs ptr

export
poke : Int -> Byte -> ByteArray -> IO ()
poke ofs b (BA ptr sz)
  = if (ofs < 0 || ofs >= sz)
      then pure ()
      else foreign FFI_C "array_poke" (Int -> Byte -> CData -> IO ()) ofs b ptr

export
pokeInt : Int -> Int -> ByteArray -> IO ()
pokeInt ofs i (BA ptr sz)
  = if (ofs < 0 || ofs+bytesPerInt > sz)
      then pure ()
      else foreign FFI_C "array_poke_int" (Int -> Int -> CData -> IO ()) ofs i ptr

export
copy : (ByteArray, Int) -> (ByteArray, Int) -> Int -> IO ()
copy (BA srcPtr srcSz, srcIx) (BA dstPtr dstSz, dstIx) count
  = if (srcIx < 0 || dstIx < 0 || (srcIx+count) > srcSz || (dstIx+count) > dstSz)
      then pure ()
      else foreign FFI_C "array_copy" (CData -> Int -> CData -> Int -> Int -> IO ()) srcPtr srcIx dstPtr dstIx count

export
fill : Int -> Int -> Byte -> ByteArray -> IO ()
fill ofs count b (BA ptr sz)
  = if (ofs < 0 || ofs+count > sz)
      then pure ()
      else foreign FFI_C "array_fill" (Int -> Int -> Byte -> CData -> IO ()) ofs count b ptr

export
size : ByteArray -> Int
size (BA ptr sz) = sz

export
compare : (ByteArray, Int) -> (ByteArray, Int) -> Int -> IO Int
compare (BA ptrL szL, ofsL) (BA ptrR szR, ofsR) count
  = if (ofsL < 0 || ofsL+count > szL || ofsR < 0 || ofsR+count > szR)
      then pure 0
      else foreign FFI_C "array_compare" (CData -> Int -> CData -> Int -> Int -> IO Int) ptrL ofsL ptrR ofsR count

export
find : Byte -> ByteArray -> Int -> Int -> IO (Maybe Int)
find b (BA ptr sz) ofs end = do
  ofs <- foreign FFI_C "array_find" (Byte -> CData -> Int -> Int -> IO Int) b ptr ofs end
  if ofs < 0
    then pure $ Nothing
    else pure $ Just ofs
