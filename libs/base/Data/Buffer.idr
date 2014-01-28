module Data.Buffer

%default total

-- !!! TODO: Open issues:
-- 1. It may be theoretically nice to represent Buffer size as
--    Fin (2 ^ WORD_BITS) instead of Nat
-- 2. Primitives take Integers when really they should take the
--    equivalent of C's size_t (ideally unboxed)
-- 3. If we had access to host system information, we could reduce
--    the needed primitives by implementing the LE/BE variants on
--    top of the native variant plus a possible swab function
-- 4. Would be nice to be able to peek/append Int, Char, and Float,
--    all have fixed (though possibly implementation-dependent) widths.
--    Currently not in place due to lack of host system introspection.
-- 5. Would be nice to be able to peek/append the vector types, but
--    for now I'm only touching the C backend which AFAICT doesn't
--    support them.
-- 6. Conversion from Fin to Integer (which, re 2, should eventually
--    be a fixed-width implementation-dependent type) is likely
--    inefficient relative to conversion from Nat to Integer

-- A contiguous chunk of n bytes
abstract
record Buffer : Nat -> Type where
  MkBuffer : ( realBuffer : prim__UnsafeBuffer ) -> Buffer n

-- Allocate an empty Buffer. The size hint can be used to avoid
-- unnecessary reallocations and copies under the hood if the
-- approximate ultimate size of the Buffer is known
public
allocate : ( hint : Nat ) -> Buffer 0
allocate = MkBuffer . prim__allocate . toIntegerNat

-- Copy a buffer. Since multiple buffers can reference the same
-- underlying chunk of memory, it may happen that a reference to
-- a relatively small bit of data might be preventing the runtime
-- from freeing a much larger chunk. copy allows giving up references
-- to the larger chunk without losing the smaller one.
public
copy : Buffer n -> Buffer n
copy = MkBuffer . prim__copy ( toIntegerNat n ) . realBuffer

-- Read a Buffer from another Buffer starting at offset
-- (i.e. create a view of a subset of the Buffer)
public
peekBufferNative : Buffer ( n + m ) -> ( offset : Fin n ) -> Buffer m
peekBufferNative ( MkBuffer real ) =
  MkBuffer . prim__peekBufferNative real . finToInteger

public
peekBufferLE : Buffer ( n + m ) -> ( offset : Fin n ) -> Buffer m
peekBufferLE = peekBufferNative

public
peekBufferBE : Buffer ( n + m ) -> ( offset : Fin n ) -> Buffer m
peekBufferBE = peekBufferNative

-- Append count repetitions of a Buffer to another Buffer
public
appendBufferNative : Buffer n        ->
                     ( count : Nat ) ->
                     Buffer m        ->
                     Buffer ( n + m * count )
appendBufferNative ( MkBuffer input ) count = MkBuffer .
  prim__appendBufferNative input ( toIntegerNat count ) . realBuffer


public
appendBufferLE : Buffer n        ->
                 ( count : Nat ) ->
                 Buffer m        ->
                 Buffer ( n + m * count )
appendBufferLE = appendBufferNative

public
appendBufferBE : Buffer n        ->
                 ( count : Nat ) ->
                 Buffer m        ->
                 Buffer ( n + m * count )
appendBufferBE = appendBufferNative

peekBits : ( prim__UnsafeBuffer -> Integer -> a ) ->
           Buffer ( n + m )   ->
           ( offset : Fin n ) ->
           a
peekBits prim ( MkBuffer real ) = prim real . finToInteger

appendBits : ( prim__UnsafeBuffer ->
               Integer            ->
               a                  ->
               prim__UnsafeBuffer ) ->
             Buffer n               ->
             ( count : Nat)         ->
             a                      ->
             Buffer ( n + count * size )
appendBits prim ( MkBuffer real ) count =
  MkBuffer . prim real ( toIntegerNat count )


-- Read a Bits8 from a Buffer starting at offset
public
peekBits8Native : Buffer ( n + 1 ) -> ( offset : Fin n ) -> Bits8
peekBits8Native = peekBits prim__peekBits8Native

public
peekBits8LE : Buffer ( n + 1 ) -> ( offset : Fin n ) -> Bits8
peekBits8LE = peekBits8Native

public
peekBits8BE : Buffer ( n + 1 ) -> ( offset : Fin n ) -> Bits8
peekBits8BE = peekBits8Native

-- Append count repetitions of a Bits8 to a Buffer
public
appendBits8Native : Buffer n        ->
                    ( count : Nat ) ->
                    Bits8           ->
                    Buffer ( n + count )
appendBits8Native = appendBits prim__appendBits8Native

public
appendBits8LE : Buffer n        ->
                ( count : Nat ) ->
                Bits8           ->
                Buffer ( n + count )
appendBits8LE = appendBits8Native

public
appendBits8BE : Buffer n        ->
                ( count : Nat ) ->
                Bits8           ->
                Buffer ( n + count )
appendBits8BE = appendBits8Native


-- Read a Bits16 in native byte order from a Buffer starting at offset
public
peekBits16Native : Buffer ( n + 2 ) -> ( offset : Fin n ) -> Bits8
peekBits16Native = peekBits prim__peekBits16Native

-- Read a little-endian Bits16 from a Buffer starting at offset
public
peekBits16LE : Buffer ( n + 2 ) -> ( offset : Fin n ) -> Bits8
peekBits16LE = peekBits prim__peekBits16LE

-- Read a big-endian Bits16 from a Buffer starting at offset
public
peekBits16BE : Buffer ( n + 2 ) -> ( offset : Fin n ) -> Bits8
peekBits16BE = peekBits prim__peekBits16LE

-- Append count repetitions of a Bits16 in native byte order to a Buffer
public
appendBits16Native : Buffer n        ->
                     ( count : Nat ) ->
                     Bits16          ->
                     Buffer ( n + 2 * count )
appendBits16Native = appendBits prim__appendBits16Native

-- Append count repetitions of a little-endian Bits16 to a Buffer
public
appendBits16LE : Buffer n        ->
                 ( count : Nat ) ->
                 Bits16          ->
                 Buffer ( n + 2 * count )
appendBits16LE = appendBits prim__appendBits16LE

-- Append count repetitions of a big-endian Bits16 to a Buffer
public
appendBits16BE : Buffer n        ->
                 ( count : Nat ) ->
                 Bits16          ->
                 Buffer ( n + 2 * count )
appendBits16BE = appendBits prim__appendBits16BE

-- Read a Bits32 in native byte order from a Buffer starting at offset
public
peekBits32Native : Buffer ( n + 4 ) -> ( offset : Fin n ) -> Bits8
peekBits32Native = peekBits prim__peekBits32Native

-- Read a little-endian Bits32 from a Buffer starting at offset
public
peekBits32LE : Buffer ( n + 4 ) -> ( offset : Fin n ) -> Bits8
peekBits32LE = peekBits prim__peekBits32LE

-- Read a big-endian Bits32 from a Buffer starting at offset
public
peekBits32BE : Buffer ( n + 4 ) -> ( offset : Fin n ) -> Bits8
peekBits32BE = peekBits prim__peekBits32LE

-- Append count repetitions of a Bits32 in native byte order to a Buffer
public
appendBits32Native : Buffer n        ->
                     ( count : Nat ) ->
                     Bits32          ->
                     Buffer ( n + 4 * count )
appendBits32Native = appendBits prim__appendBits32Native

-- Append count repetitions of a little-endian Bits32 to a Buffer
public
appendBits32LE : Buffer n        ->
                 ( count : Nat ) ->
                 Bits32          ->
                 Buffer ( n + 4 * count )
appendBits32LE = appendBits prim__appendBits32LE

-- Append count repetitions of a big-endian Bits32 to a Buffer
public
appendBits32BE : Buffer n        ->
                 ( count : Nat ) ->
                 Bits32          ->
                 Buffer ( n + 4 * count )
appendBits32BE = appendBits prim__appendBits32BE

-- Read a Bits64 in native byte order from a Buffer starting at offset
public
peekBits64Native : Buffer ( n + 8 ) -> ( offset : Fin n ) -> Bits8
peekBits64Native = peekBits prim__peekBits64Native

-- Read a little-endian Bits64 from a Buffer starting at offset
public
peekBits64LE : Buffer ( n + 8 ) -> ( offset : Fin n ) -> Bits8
peekBits64LE = peekBits prim__peekBits64LE

-- Read a big-endian Bits64 from a Buffer starting at offset
public
peekBits64BE : Buffer ( n + 8 ) -> ( offset : Fin n ) -> Bits8
peekBits64BE = peekBits prim__peekBits64LE

-- Append count repetitions of a Bits64 in native byte order to a Buffer
public
appendBits64Native : Buffer n        ->
                     ( count : Nat ) ->
                     Bits64          ->
                     Buffer ( n + 8 * count )
appendBits64Native = appendBits prim__appendBits64Native

-- Append count repetitions of a little-endian Bits64 to a Buffer
public
appendBits64LE : Buffer n        ->
                 ( count : Nat ) ->
                 Bits64          ->
                 Buffer ( n + 8 * count )
appendBits64LE = appendBits prim__appendBits64LE

-- Append count repetitions of a big-endian Bits64 to a Buffer
public
appendBits64BE : Buffer n        ->
                 ( count : Nat ) ->
                 Bits64          ->
                 Buffer ( n + 8 * count )
appendBits64BE = appendBits prim__appendBits64BE
