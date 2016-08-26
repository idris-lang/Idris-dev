module Main

import Data.Bytes as B
import Data.ByteArray as BA

-- %flag C "-g3 -ggdb -O0"
%link C "array.o"

initialBuf : Bytes
initialBuf = pack . concat $ replicate 128 block
  where
    block : List Byte
    block = [10,32,1,10,100,32,1,10,255,32,1,10,1,10,255,32,1,10,255,32,1,10,255,32,1,10]

unRLE : Bytes -> Bytes
unRLE = fst . iterateL phi (empty, Nothing)
  where
    phi : (Bytes, Maybe Byte) -> Byte -> Result (Bytes, Maybe Byte)
    phi (bs, Nothing)  b = Cont (bs, Just b)
    phi (bs, Just cnt) b = Cont (bs ++ pack (replicate (cast $ prim__zextB8_Int cnt) b), Nothing)

unit : Int -> Byte -> IO ()
unit n b =
    let expanded = unRLE initialBuf
      in let elines = map (flip snoc b) (asciiLines expanded)
        in printLn $ (show b ++ "/" ++ show n, length expanded, length elines)

alloc : Int -> Int -> IO Int
alloc x 0 = pure x
alloc x i = do
  -- allocate an array
  arr <- BA.allocate (64 * 1024 * 1024)
  -- write "i" at offset 63M
  BA.pokeInt (63*1024*1024) i arr
  -- read number from offset 63M
  j <- BA.peekInt (63*1024*1024) arr
  -- count matches
  alloc (x + if i == j then 1 else 0) (i - 1)

main : IO ()
main = do
    -- First allocate 1024 64M arrays to break the C heap if there's a bug
    alloc 0 1024 >>= printLn

    -- Then, test Bytes
    traverse_ (unit n . prim__truncInt_B8) [1..n]
  where
    n = 8
