module Data.IORef

%default total

||| A mutable variable in the IO monad.
export
data IORef a = MkIORef a

public export
interface HasReference (ffi : FFI) where
  newIORef' : a -> IO' ffi (IORef a)
  readIORef' : IORef a -> IO' ffi a
  writeIORef' : IORef a -> a -> IO' ffi ()

export
modifyIORef': HasReference ffi => IORef a -> (a -> a) -> IO' ffi ()
modifyIORef' ref fn =
  do
    val <- readIORef' ref
    writeIORef' ref (fn val)

export
implementation HasReference FFI_C where
  newIORef' val
    = do MkRaw ref <- foreign FFI_C "idris_newRef" (Raw a -> IO (Raw a)) (MkRaw val)
         pure (MkIORef ref)
  readIORef' (MkIORef ref)
    = do MkRaw val <- foreign FFI_C "idris_readRef" (Raw a -> IO (Raw a)) (MkRaw ref)
         pure val
  writeIORef' (MkIORef ref) val
    = foreign FFI_C "idris_writeRef" (Raw a -> Raw a -> IO ())
              (MkRaw ref) (MkRaw val)

export
implementation HasReference FFI_JS where
  newIORef' val =
    (MkIORef . believe_me) <$> foreign FFI_JS "{val: %0}" (Ptr -> JS_IO Ptr) (believe_me val)
  readIORef' (MkIORef ref) =
    believe_me <$> foreign FFI_JS "%0.val" (Ptr -> JS_IO Ptr) (believe_me ref)
  writeIORef' (MkIORef ref) val =
    foreign FFI_JS "%0.val = %1" (Ptr -> Ptr -> JS_IO ()) (believe_me ref) (believe_me val)

||| Build a new IORef
export
newIORef : a -> IO (IORef a)
newIORef = newIORef'

||| read the value of an IORef
export
readIORef : IORef a -> IO a
readIORef = readIORef'

||| write the value of an IORef
export
writeIORef : IORef a -> a -> IO ()
writeIORef = writeIORef'

||| mutate the contents of an IORef
export
modifyIORef : IORef a -> (a -> a) -> IO ()
modifyIORef = modifyIORef'
