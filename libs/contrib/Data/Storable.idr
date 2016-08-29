module Data.Storable

%access public export

interface Storable a where
    sizeOf : a -> Int
    alignOf : a -> Int
    peek : Ptr -> Int -> IO a
    poke : Ptr -> Int -> a -> IO ()

Storable Bits8 where
    sizeOf _ = 1
    alignOf _ = 1
    peek p offset = prim_peek8 p offset
    poke p offset val = do
        _ <- prim_poke8 p offset val
        pure ()

Storable Bits16 where
    sizeOf _ = 2
    alignOf _ = 2
    peek p offset = prim_peek16 p offset
    poke p offset val = do
        _ <- prim_poke16 p offset val
        pure ()

Storable Bits32 where
    sizeOf _ = 4
    alignOf _ = 4
    peek p offset = prim_peek32 p offset
    poke p offset val = do
        _ <- prim_poke32 p offset val
        pure ()

Storable Bits64 where
    sizeOf _ = 8
    alignOf _ = 8
    peek p offset = prim_peek64 p offset
    poke p offset val = do
        _ <- prim_poke64 p offset val
        pure ()
