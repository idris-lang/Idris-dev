module Util.Zlib (decompressEither) where

-- From http://stackoverflow.com/questions/10043102/how-to-catch-the-decompress-ioerror/10045963#10045963
import Codec.Compression.Zlib.Internal
import Data.ByteString.Lazy (ByteString, fromChunks)
import Control.Arrow (right)

decompressEither :: ByteString -> Either (DecompressError, String) ByteString
decompressEither = finalise
                            . foldDecompressStream cons nil err
                            . decompressWithErrors zlibFormat defaultDecompressParams
  where err errorCode errorString = Left (errorCode, errorString)
        nil = Right []
        cons chunk = right (chunk :)
        finalise = right fromChunks
