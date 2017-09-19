module Data.IORef

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
