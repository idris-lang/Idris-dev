module Data.IORef

public export
interface HasReference (ffi : FFI) where
  IORef' : Type -> Type
  newIORef' : a -> IO' ffi (IORef' a)
  readIORef' : IORef' a -> IO' ffi a
  writeIORef' : IORef' a -> a -> IO' ffi ()

export
modifyIORef': HasReference ffi => IORef' {ffi = ffi} a -> (a -> a) -> IO' ffi ()
modifyIORef' ref fn =
  do
    val <- readIORef' ref
    writeIORef' ref (fn val)

export
implementation HasReference FFI_C where
  IORef' = Raw
  newIORef' val =
    foreign FFI_C "idris_newRef" (Raw a -> IO (Raw a)) (MkRaw val)
  readIORef' ref =
    do
      MkRaw val <- foreign FFI_C "idris_readRef" (Raw a -> IO (Raw a)) ref
      pure val
  writeIORef' ref val =
    foreign FFI_C "idris_writeRef" (Raw a -> Raw a -> IO ())
              ref (MkRaw val)

export
IORef : Type -> Type
IORef = IORef' {ffi = FFI_C}

export
newIORef : a -> IO (IORef a)
newIORef = newIORef'

export
readIORef : IORef a -> IO a
readIORef = readIORef'

export
writeIORef : IORef a -> a -> IO ()
writeIORef = writeIORef'

export
modifyIORef : IORef a -> (a -> a) -> IO ()
modifyIORef = modifyIORef'
{-
export
data IORef a = MkIORef a

export
newIORef : a -> IO (IORef a)
newIORef val
    = do MkRaw ref <- foreign FFI_C "idris_newRef" (Raw a -> IO (Raw a)) (MkRaw val)
         pure (MkIORef ref)

export
readIORef : IORef a -> IO a
readIORef (MkIORef ref)
    = do MkRaw val <- foreign FFI_C "idris_readRef" (Raw a -> IO (Raw a)) (MkRaw ref)
         pure val

export
writeIORef : IORef a -> a -> IO ()
writeIORef (MkIORef old) val
    = foreign FFI_C "idris_writeRef" (Raw a -> Raw a -> IO ())
              (MkRaw old) (MkRaw val)

export
modifyIORef : IORef a -> (a -> a) -> IO ()
modifyIORef ref fn
    = do val <- readIORef ref
         writeIORef ref (fn val)
-}
