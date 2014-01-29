module Data.Buffer

%default total

-- !!! TODO: Open issues:
-- 1. It may be theoretically nice to represent Buffer size as
--    Fin (2 ^ WORD_BITS) instead of Nat
-- 2. Primitives take Bits64 when really they should take the
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
-- 6. Conversion from Fin to Bits64 (which, re 2, should eventually
--    be a fixed-width implementation-dependent type) is likely
--    inefficient relative to conversion from Nat to Bits64

-- A contiguous chunk of n bytes
abstract
record Buffer : Nat -> Type where
  MkBuffer : ( realBuffer : prim__UnsafeBuffer ) -> Buffer n

bitsFromNat : Nat -> Bits64
bitsFromNat Z     = 0
bitsFromNat (S k) = 1 + bitsFromNat k

bitsFromFin : Fin n -> Bits64
bitsFromFin fZ     = 0
bitsFromFin (fS k) = 1 + bitsFromFin k

-- Allocate an empty Buffer. The size hint can be used to avoid
-- unnecessary reallocations and copies under the hood if the
-- approximate ultimate size of the Buffer is known. Users can assume
-- the new Buffer is word-aligned.
public
allocate : ( hint : Nat ) -> Buffer 0
allocate = MkBuffer . prim__allocate . bitsFromNat

-- Copy a buffer. Since multiple buffers can reference the same
-- underlying chunk of memory, it may happen that a reference to
-- a relatively small bit of data might be preventing the runtime
-- from freeing a much larger chunk. copy allows giving up references
-- to the larger chunk without losing the smaller one.
%assert_total
public
copy : Buffer n -> Buffer n
copy { n } = MkBuffer . prim__copy ( bitsFromNat n ) . realBuffer

-- Read a Buffer from another Buffer starting at offset
-- (i.e. create a view of a subset of the Buffer)
%assert_total
public
peekBufferNative : Buffer ( m + n )           ->
                   ( offset : Fin ( n + 1 ) ) ->
                   Buffer m
peekBufferNative ( MkBuffer real ) =
  MkBuffer . prim__peekBufferNative real . bitsFromFin

public
peekBufferLE : Buffer ( m + n )           ->
               ( offset : Fin ( n + 1 ) ) ->
               Buffer m
peekBufferLE = peekBufferNative

public
peekBufferBE : Buffer ( m + n )            ->
               ( offset : Fin  ( n + 1 ) ) ->
               Buffer m
peekBufferBE = peekBufferNative

-- Append count repetitions of a Buffer to another Buffer
%assert_total
public
appendBufferNative : Buffer n        ->
                     ( count : Nat ) ->
                     Buffer m        ->
                     Buffer ( n + m * count )
appendBufferNative { n } { m } ( MkBuffer input ) count =
  MkBuffer . app . realBuffer
  where
    nBits : Bits64
    nBits = bitsFromNat n
    mBits : Bits64
    mBits = bitsFromNat m
    cBits : Bits64
    cBits = bitsFromNat count
    app = prim__appendBufferNative input nBits cBits mBits

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


peekBits : ( prim__UnsafeBuffer -> Bits64 -> a ) ->
           Buffer ( m + n )   ->
           ( offset : Fin ( n + 1 ) ) ->
           a
peekBits prim ( MkBuffer real ) = prim real . bitsFromFin

appendBits : ( prim__UnsafeBuffer ->
               Bits64             ->
               Bits64             ->
               a                  ->
               prim__UnsafeBuffer ) ->
             Buffer n               ->
             ( count : Nat)         ->
             a                      ->
             Buffer ( n + count * size )
appendBits { n } prim ( MkBuffer real ) count =
  MkBuffer . prim real ( bitsFromNat n ) ( bitsFromNat count )


-- Read a Bits8 from a Buffer starting at offset
%assert_total
public
peekBits8Native : Buffer ( 1 + n )           ->
                  ( offset : Fin ( n + 1 ) ) ->
                  Bits8
peekBits8Native = peekBits { m = 1 } prim__peekB8Native

%assert_total
public
peekBits8LE : Buffer ( 1 + n ) -> ( offset : Fin ( n + 1 ) ) -> Bits8
peekBits8LE = peekBits { m = 1 } prim__peekB8LE

%assert_total
public
peekBits8BE : Buffer ( 1 + n ) -> ( offset : Fin ( n + 1 ) ) -> Bits8
peekBits8BE = peekBits { m = 1 } prim__peekB8BE

-- Append count repetitions of a Bits8 to a Buffer
%assert_total
public
appendBits8Native : Buffer n        ->
                    ( count : Nat ) ->
                    Bits8           ->
                    Buffer ( n + count * 1 )
appendBits8Native = appendBits prim__appendB8Native

%assert_total
public
appendBits8LE : Buffer n        ->
                ( count : Nat ) ->
                Bits8           ->
                Buffer ( n + count * 1 )
appendBits8LE = appendBits prim__appendB8LE

%assert_total
public
appendBits8BE : Buffer n        ->
                ( count : Nat ) ->
                Bits8           ->
                Buffer ( n + count * 1 )
appendBits8BE = appendBits prim__appendB8BE


-- Read a Bits16 in native byte order from a Buffer starting at offset
%assert_total
public
peekBits16Native : Buffer ( 2 + n )           ->
                   ( offset : Fin ( n + 1 ) ) ->
                   Bits16
peekBits16Native = peekBits { m = 2 } prim__peekB16Native

-- Read a little-endian Bits16 from a Buffer starting at offset
%assert_total
public
peekBits16LE : Buffer ( 2 + n ) -> ( offset : Fin ( n + 1 ) ) -> Bits16
peekBits16LE = peekBits { m = 2 } prim__peekB16LE

-- Read a big-endian Bits16 from a Buffer starting at offset
%assert_total
public
peekBits16BE : Buffer ( 2 + n ) -> ( offset : Fin ( n + 1 ) ) -> Bits16
peekBits16BE = peekBits { m = 2 } prim__peekB16BE

-- Append count repetitions of a Bits16 in native byte order to a Buffer
%assert_total
public
appendBits16Native : Buffer n        ->
                     ( count : Nat ) ->
                     Bits16          ->
                     Buffer ( n + count * 2 )
appendBits16Native = appendBits prim__appendB16Native

-- Append count repetitions of a little-endian Bits16 to a Buffer
%assert_total
public
appendBits16LE : Buffer n        ->
                 ( count : Nat ) ->
                 Bits16          ->
                 Buffer ( n + count * 2 )
appendBits16LE = appendBits prim__appendB16LE

-- Append count repetitions of a big-endian Bits16 to a Buffer
%assert_total
public
appendBits16BE : Buffer n        ->
                 ( count : Nat ) ->
                 Bits16          ->
                 Buffer ( n + count * 2 )
appendBits16BE = appendBits prim__appendB16BE

-- Read a Bits32 in native byte order from a Buffer starting at offset
%assert_total
public
peekBits32Native : Buffer ( 4 + n )           ->
                   ( offset : Fin ( n + 1 ) ) ->
                   Bits32
peekBits32Native = peekBits { m = 4 } prim__peekB32Native

-- Read a little-endian Bits32 from a Buffer starting at offset
%assert_total
public
peekBits32LE : Buffer ( 4 + n ) -> ( offset : Fin ( n + 1 ) ) -> Bits32
peekBits32LE = peekBits { m = 4 } prim__peekB32LE

-- Read a big-endian Bits32 from a Buffer starting at offset
%assert_total
public
peekBits32BE : Buffer ( 4 + n ) -> ( offset : Fin ( n + 1 ) ) -> Bits32
peekBits32BE = peekBits { m = 4 } prim__peekB32BE

-- Append count repetitions of a Bits32 in native byte order to a Buffer
%assert_total
public
appendBits32Native : Buffer n        ->
                     ( count : Nat ) ->
                     Bits32          ->
                     Buffer ( n + count * 4 )
appendBits32Native = appendBits prim__appendB32Native

-- Append count repetitions of a little-endian Bits32 to a Buffer
%assert_total
public
appendBits32LE : Buffer n        ->
                 ( count : Nat ) ->
                 Bits32          ->
                 Buffer ( n + count * 4 )
appendBits32LE = appendBits prim__appendB32LE

-- Append count repetitions of a big-endian Bits32 to a Buffer
%assert_total
public
appendBits32BE : Buffer n        ->
                 ( count : Nat ) ->
                 Bits32          ->
                 Buffer ( n + count * 4 )
appendBits32BE = appendBits prim__appendB32BE

-- Read a Bits64 in native byte order from a Buffer starting at offset
%assert_total
public
peekBits64Native : Buffer ( 8 + n )           ->
                   ( offset : Fin ( n + 1 ) ) ->
                   Bits64
peekBits64Native = peekBits { m = 8 } prim__peekB64Native

-- Read a little-endian Bits64 from a Buffer starting at offset
%assert_total
public
peekBits64LE : Buffer ( 8 + n ) -> ( offset : Fin ( n + 1 ) ) -> Bits64
peekBits64LE = peekBits { m = 8 } prim__peekB64LE

-- Read a big-endian Bits64 from a Buffer starting at offset
%assert_total
public
peekBits64BE : Buffer ( 8 + n ) -> ( offset : Fin ( n + 1 ) ) -> Bits64
peekBits64BE = peekBits { m = 8 } prim__peekB64BE

-- Append count repetitions of a Bits64 in native byte order to a Buffer
%assert_total
public
appendBits64Native : Buffer n        ->
                     ( count : Nat ) ->
                     Bits64          ->
                     Buffer ( n + count * 8 )
appendBits64Native = appendBits prim__appendB64Native

-- Append count repetitions of a little-endian Bits64 to a Buffer
%assert_total
public
appendBits64LE : Buffer n        ->
                 ( count : Nat ) ->
                 Bits64          ->
                 Buffer ( n + count * 8 )
appendBits64LE = appendBits prim__appendB64LE

-- Append count repetitions of a big-endian Bits64 to a Buffer
%assert_total
public
appendBits64BE : Buffer n        ->
                 ( count : Nat ) ->
                 Bits64          ->
                 Buffer ( n + count * 8 )
appendBits64BE = appendBits prim__appendB64BE
