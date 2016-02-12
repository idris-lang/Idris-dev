module Data.Hash

import Data.Vect

%access public export
%default total

{- A general purpose Hashing library (not cryptographic)

   The core hash is djb2, which is very fast but does not have the best distribution
   Source: http://www.cse.yorku.ca/~oz/hash.html

   The salted version and the magic salt are copied from Haskell's bloomfilter library
   Source: https://hackage.haskell.org/package/bloomfilter-2.0.0.0/docs/src/Data-BloomFilter-Hash.html#Hashable
-}

||| A type that can be hashed
interface Hashable a where
  saltedHash64 : a -> Bits64 -> Bits64 -- value to hash, salt, hash

||| Computes a non cryptographic hash
hash : Hashable a => a -> Bits64
hash x = saltedHash64 x 0x16fc397cf62f64d3

||| Given a user provided salt, computes a non cryptographic hash.
||| This version is meant to mitigate hash-flooding DoS attacks.
saltedHash : Hashable a => Bits64 -> a -> Bits64
saltedHash salt x = saltedHash64 x salt


||| Nth byte of a Bits64
private
byte : Bits64 -> Bits64 -> Bits64
byte n w = prim__lshrB64 (prim__andB64 mask w) offset
  where offset = 8*n
        mask = prim__shlB64 0xff (the Bits64 offset)

||| Modulo of an integer, downsized to a Bits64
private
mod64 : Integer -> Bits64
mod64 i = assert_total $ prim__truncBigInt_B64 (abs i `mod` 0xffffffffffffffff)

implementation Hashable Bits64 where
  saltedHash64 w salt = foldr (\b,acc => (acc `prim__shlB64` 10) + acc + b)
                              salt
                              [byte (fromInteger n) w | n <- [7,6..0]] -- djb2 hash function. Not meant for crypto

implementation Hashable Integer where
  saltedHash64 i = saltedHash64 (mod64 i)

implementation Hashable () where
  saltedHash64 _ salt = salt

implementation Hashable Bool where
  saltedHash64 True  = saltedHash64 (the Bits64 1)
  saltedHash64 False = saltedHash64 (the Bits64 0)

implementation Hashable Int where
  saltedHash64 w = saltedHash64 (prim__zextInt_B64 w)

implementation Hashable Char where
  saltedHash64 w = saltedHash64 (the Int (cast w))

implementation Hashable Bits8 where
  saltedHash64 w = saltedHash64 (prim__zextB8_B64 w)

implementation Hashable Bits16 where
  saltedHash64 w = saltedHash64 (prim__zextB16_B64 w)

implementation Hashable Bits32 where
  saltedHash64 w = saltedHash64 (prim__zextB32_B64 w)

implementation Hashable a => Hashable (Maybe a) where
  saltedHash64 Nothing  salt = salt
  saltedHash64 (Just k) salt = saltedHash64 k salt

implementation (Hashable a, Hashable b) => Hashable (a, b) where
  saltedHash64 (a,b) salt = saltedHash64 b (saltedHash64 a salt)

implementation Hashable a => Hashable (List a) where
  saltedHash64 l salt = foldr (\c,acc => saltedHash64 c acc) salt l

implementation Hashable a => Hashable (Vect n a) where
  saltedHash64 l salt = foldr (\c,acc => saltedHash64 c acc) salt l

implementation Hashable String where
  saltedHash64 s = saltedHash64 (unpack s)
