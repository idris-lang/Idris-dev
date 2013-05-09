module Effect.Memory

import Effects
import Control.IOExcept

%access public

abstract
data MemoryChunk : Nat -> Nat -> Type where
     CH : Ptr -> MemoryChunk size initialized

abstract
data RawMemory : Effect where
     Allocate   : (n : Nat) ->
                  RawMemory () (MemoryChunk n 0) ()
     Free       : RawMemory (MemoryChunk n i) () ()
     Initialize : Bits8 ->
                  (size : Nat) ->
                  so (i + size <= n) ->
                  RawMemory (MemoryChunk n i) (MemoryChunk n (i + size)) ()
     Peek       : (offset : Nat) ->
                  (size : Nat) ->
                  so (offset + size <= i) ->
                  RawMemory (MemoryChunk n i) (MemoryChunk n i) (Vect Bits8 size)
     Poke       :  (offset : Nat) ->
                  (Vect Bits8 size) ->
                  so (offset <= i && offset + size <= n) ->
                  RawMemory (MemoryChunk n i) (MemoryChunk n (max i (offset + size))) ()
     Move       : (src : MemoryChunk src_size src_init) ->
                  (dst_offset : Nat) ->
                  (src_offset : Nat) ->
                  (size : Nat) ->
                  so (dst_offset <= dst_init && dst_offset + size <= dst_size) ->
                  so (src_offset + size <= src_init) ->
                  RawMemory (MemoryChunk dst_size dst_init)
                            (MemoryChunk dst_size (max dst_init (dst_offset + size))) ()
     GetRawPtr  : RawMemory (MemoryChunk n i) (MemoryChunk n i) (MemoryChunk n i)

private
do_malloc : Nat -> IOExcept String Ptr
do_malloc size with (fromInteger (cast size) == size)
  | True  = do ptr <- ioe_lift $ mkForeign (FFun "malloc" [FInt] FPtr) (cast size)
               fail  <- ioe_lift $ nullPtr ptr
               if fail then ioe_fail "Cannot allocate memory"
               else return ptr
  | False = ioe_fail "The target architecture does not support adressing enough memory"

private
do_memset : Ptr -> Nat -> Bits8 -> Nat -> IO ()
do_memset ptr offset c size
  = mkForeign (FFun "idris_memset" [FPtr, FInt, FChar, FInt] FUnit)
              ptr (cast offset) c (cast size)

private
do_free : Ptr -> IO ()
do_free ptr = mkForeign (FFun "free" [FPtr] FUnit) ptr

private
do_memmove : Ptr -> Ptr -> Nat -> Nat -> Nat -> IO ()
do_memmove dest src dest_offset src_offset size
  = mkForeign (FFun "idris_memmove" [FPtr, FPtr, FInt, FInt, FInt] FUnit)
              dest src (cast dest_offset) (cast src_offset) (cast size)

private
do_peek : Ptr -> Nat -> (size : Nat) -> IO (Vect Bits8 size)
do_peek _   _       O = return (Prelude.Vect.Nil)
do_peek ptr offset (S n)
  = do b <- mkForeign (FFun "idris_peek" [FPtr, FInt] FChar) ptr (cast offset)
       bs <- do_peek ptr (S offset) n
       Prelude.Monad.return (Prelude.Vect.(::) b bs)

private
do_poke : Ptr -> Nat -> Vect Bits8 size -> IO ()
do_poke _   _      []     = return ()
do_poke ptr offset (b::bs)
  = do mkForeign (FFun "idris_poke" [FPtr, FInt, FChar] FUnit) ptr (cast offset) b
       do_poke ptr (S offset) bs

instance Handler RawMemory (IOExcept String) where
  handle () (Allocate n) k
    = do ptr <- do_malloc n
         k (CH ptr) ()
  handle {res = MemoryChunk _ offset} (CH ptr) (Initialize c size _) k
    = ioe_lift (do_memset ptr offset c size) $> k (CH ptr) ()
  handle (CH ptr) (Free) k
    = ioe_lift (do_free ptr) $> k () ()
  handle (CH ptr) (Peek offset size _) k
    = do res <- ioe_lift (do_peek ptr offset size)
         k (CH ptr) res
  handle (CH ptr) (Poke offset content _) k
    = do ioe_lift (do_poke ptr offset content)
         k (CH ptr) ()
  handle (CH dest_ptr) (Move (CH src_ptr) dest_offset src_offset size _ _) k
    = do ioe_lift (do_memmove dest_ptr src_ptr dest_offset src_offset size)
         k (CH dest_ptr) ()
  handle chunk (GetRawPtr) k
    = k chunk chunk

RAW_MEMORY : Type -> EFFECT
RAW_MEMORY t = MkEff t RawMemory

allocate : (n : Nat) -> EffM m [RAW_MEMORY ()] [RAW_MEMORY (MemoryChunk n 0)] ()
allocate size = Allocate size

initialize : {i : Nat} ->
             {n : Nat} ->
             Bits8 ->
             (size : Nat) ->
             so (i + size <= n) ->
             EffM m [RAW_MEMORY (MemoryChunk n i)] [RAW_MEMORY (MemoryChunk n (i + size))] ()
initialize c size prf = Initialize c size prf

free : EffM m [RAW_MEMORY (MemoryChunk n i)] [RAW_MEMORY ()] ()
free = Free

peek : {i : Nat} ->
       (offset : Nat) ->
       (size : Nat) ->
       so (offset + size <= i) ->
       Eff m [RAW_MEMORY (MemoryChunk n i)] (Vect Bits8 size)
peek offset size prf = Peek offset size prf

poke : {n : Nat} ->
       {i : Nat} ->
       (offset : Nat) ->
       Vect Bits8 size ->
       so (offset <= i && offset + size <= n) ->
       EffM m [RAW_MEMORY (MemoryChunk n i)] [RAW_MEMORY (MemoryChunk n (max i (offset + size)))] ()
poke offset content prf = Poke offset content prf

private
getRawPtr : Eff m [RAW_MEMORY (MemoryChunk n i)] (MemoryChunk n i)
getRawPtr = GetRawPtr

private
move' : {dst_size : Nat} ->
        {dst_init : Nat} ->
        {src_init : Nat} ->
        (src_ptr : MemoryChunk src_size src_init) ->
        (dst_offset : Nat) ->
        (src_offset : Nat) ->
        (size : Nat) ->
        so (dst_offset <= dst_init && dst_offset + size <= dst_size) ->
        so (src_offset + size <= src_init) ->
        EffM m [RAW_MEMORY (MemoryChunk dst_size dst_init)]
               [RAW_MEMORY (MemoryChunk dst_size (max dst_init (dst_offset + size)))] ()
move' src_ptr dst_offset src_offset size dst_bounds src_bounds
  = Move src_ptr dst_offset src_offset size dst_bounds src_bounds

data MoveDescriptor = Dst | Src

move : {dst_size : Nat} ->
       {dst_init : Nat} ->
       {src_size : Nat} ->
       {src_init : Nat} ->
       (dst_offset : Nat) ->
       (src_offset : Nat) ->
       (size : Nat) ->
       so (dst_offset <= dst_init && dst_offset + size <= dst_size) ->
       so (src_offset + size <= src_init) ->
       EffM m [ Dst ::: RAW_MEMORY (MemoryChunk dst_size dst_init)
              , Src ::: RAW_MEMORY (MemoryChunk src_size src_init)]
              [ Dst ::: RAW_MEMORY (MemoryChunk dst_size (max dst_init (dst_offset + size)))
              , Src ::: RAW_MEMORY (MemoryChunk src_size src_init)] ()
move dst_offset src_offset size dst_bounds src_bounds
  = do src_ptr <- Src :- getRawPtr
       Dst :- move' src_ptr dst_offset src_offset size dst_bounds src_bounds
       return ()
