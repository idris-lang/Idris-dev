module Data.Buffer

%include C "idris_buffer.h"

||| A buffer is a pointer to a sized, unstructured, mutable chunk of memory
export
record Buffer where
  constructor MkBuffer
  ||| Raw bytes, as a pointer to a block of memory
  rawdata : ManagedPtr -- let Idris run time manage the memory
  ||| Cached size of block
  buf_size : Int
  ||| Next location to read/write (e.g. when reading from file)
  location : Int 

||| Create a new buffer 'size' bytes long. Returns 'Nothing' if allocation
||| fails
export
newBuffer : (size : Int) -> IO (Maybe Buffer)
newBuffer size = do bptr <- foreign FFI_C "idris_newBuffer" (Int -> IO Ptr) 
                                    size
                    bad <- nullPtr bptr
                    if bad then pure Nothing
                           else pure (Just (MkBuffer (prim__registerPtr bptr (size + 8)) size 0))

||| Reset the 'next location' pointer of the buffer to 0.
||| The 'next location' pointer gives the location for the next file read/write
||| so resetting this means you can write it again
export
resetBuffer : Buffer -> Buffer
resetBuffer buf = record { location = 0 } buf

||| Return the space available in the buffer
export
rawSize : Buffer -> IO Int
rawSize b = foreign FFI_C "idris_getBufferSize" (ManagedPtr -> IO Int) (rawdata b)

export
size : Buffer -> Int
size b = buf_size b

||| Set the byte at position 'loc' to 'val'.
||| Does nothing if the location is outside the bounds of the buffer
export
setByte : Buffer -> (loc : Int) -> (val : Bits8) -> IO ()
setByte b loc val
    = foreign FFI_C "idris_setBufferByte" (ManagedPtr -> Int -> Bits8 -> IO ())
              (rawdata b) loc val

||| Set the byte at position 'loc' to 'val'.
||| Does nothing if the location is out of bounds of the buffer, or the string
||| is too long for the location
export
setString : Buffer -> Int -> String -> IO ()
setString b loc val
    = foreign FFI_C "idris_setBufferString" (ManagedPtr -> Int -> String -> IO ())
              (rawdata b) loc val

||| Copy data from 'src' to 'dest'. Reads 'len' bytes starting at position
||| 'start' in 'src', and writes them starting at position 'loc' in 'dest'.
||| Does nothing if a location is out of bounds, or there is not enough room
export
copyData : (src : Buffer) -> (start, len : Int) ->
           (dest : Buffer) -> (loc : Int) -> IO ()
copyData src start len dest loc 
    = foreign FFI_C "idris_copyBuffer" (ManagedPtr -> Int -> Int -> ManagedPtr -> Int -> IO ())
              (rawdata src) start len (rawdata dest) loc

||| Return the value at the given location in the buffer
export
getByte : Buffer -> (loc : Int) -> IO Bits8
getByte b loc
    = foreign FFI_C "idris_getBufferByte" (ManagedPtr -> Int -> IO Bits8)
              (rawdata b) loc 

||| Read 'maxbytes' into the buffer from a file, returning a new
||| buffer with the 'locaton' pointer moved along
export
readBufferFromFile : File -> Buffer -> (maxbytes : Int) -> IO Buffer
readBufferFromFile (FHandle h) buf max
    = do numread <- foreign FFI_C "idris_readBuffer" (Ptr -> ManagedPtr -> Int -> Int -> IO Int)
                       h (rawdata buf) (location buf) max
         pure (record { location $= (+numread) } buf)

||| Write 'maxbytes' from the buffer from a file, returning a new
||| buffer with the 'locaton' pointer moved along
export
writeBufferToFile : File -> Buffer -> (maxbytes : Int) -> IO Buffer
writeBufferToFile (FHandle h) buf max
    = do let maxwrite = size buf - location buf
         let max' = if maxwrite < max then maxwrite else max
         foreign FFI_C "idris_writeBuffer" (Ptr -> ManagedPtr -> Int -> Int -> IO ())
                 h (rawdata buf) (location buf) max'
         pure (record { location $= (+max') } buf)

||| Return the contents of the buffer as a list
export
bufferData : Buffer -> IO (List Bits8)
bufferData b = do let len = size b
                  unpackTo [] len
  where unpackTo : List Bits8 -> Int -> IO (List Bits8)
        unpackTo acc 0 = pure acc
        unpackTo acc loc = do val <- getByte b (loc - 1)
                              unpackTo (val :: acc) 
                                       (assert_smaller loc (loc - 1))

||| Create a new buffer, copying the contents of the old buffer to the new.
||| Returns 'Nothing' if resizing fails
export
resizeBuffer : Buffer -> Int -> IO (Maybe Buffer)
resizeBuffer old newsize
    = do Just buf <- newBuffer newsize
              | Nothing => pure Nothing
         -- If the new buffer is smaller than the old one, just copy what
         -- fits
         let oldsize = size old
         let len = if newsize < oldsize then newsize else oldsize
         copyData old 0 len buf 0
         pure (Just buf)
