module Data.IOArray

-- Raw access to IOArrays. This interface is unsafe because there's no
-- bounds checking, and is merely intended to provide primitive access via
-- the RTS. Safe interfaces (either with run time or compile time
-- bounds checking) can be implemented on top of this

-- Implemented entirely by the array primitives in the RTS
data ArrayData : Type -> Type where

export
data IOArray elem = MkIOArray (ArrayData elem)

||| Create a new array of the given size, with all entries set to the
||| given default element.
export
newArray : Int -> elem -> IO (IOArray elem)
newArray size default
    = do vm <- getMyVM
         MkRaw p <- foreign FFI_C "idris_newArray"
                          (Ptr -> Int -> Raw elem -> IO (Raw (ArrayData elem)))
                          vm size (MkRaw default)
         pure (MkIOArray p)

||| Write an element at a location in an array. 
||| There is *no* bounds checking, hence this is unsafe. Safe interfaces can
||| be implemented on top of this, either with a run time or compile time
||| check.
export
unsafeWriteArray : IOArray elem -> Int -> elem -> IO ()
unsafeWriteArray (MkIOArray p) i val
    = foreign FFI_C "idris_arraySet"
                    (Raw (ArrayData elem) -> Int -> Raw elem -> IO ())
                    (MkRaw p) i (MkRaw val)

||| Read the element at a location in an array. 
||| There is *no* bounds checking, hence this is unsafe. Safe interfaces can
||| be implemented on top of this, either with a run time or compile time
||| check.
export
unsafeReadArray : IOArray elem -> Int -> IO elem
unsafeReadArray (MkIOArray p) i
    = do MkRaw val <- foreign FFI_C "idris_arrayGet"
                              (Raw (ArrayData elem) -> Int -> IO (Raw elem))
                              (MkRaw p) i
         pure val

