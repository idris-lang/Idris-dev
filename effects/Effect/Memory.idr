module Effect.Memory

import Effects
import Control.IOExcept

%access public

abstract
data MemoryChunk : Nat -> Type where
     CH : Ptr -> (size : Nat) -> MemoryChunk size

abstract
data RawMemory : Effect where
     Allocate  : (n : Nat) ->
                 RawMemory () (MemoryChunk n) ()
     Free      : RawMemory (MemoryChunk n) () ()
     Peek      : (offset : Nat) ->
                 (size : Nat) ->
                 so (offset + size <= n) ->
                 RawMemory (MemoryChunk n) (MemoryChunk n) (Vect Bits8 size)
     Poke      :  (offset : Nat) ->
                 (Vect Bits8 size) ->
                 so (offset + size <= n) ->
                 RawMemory (MemoryChunk n) (MemoryChunk n) ()
     Move      : (src : MemoryChunk m) ->
                 (dest_offset : Nat) ->
                 (src_offset : Nat) ->
                 (size : Nat) ->
                 so (dest_offset + size <= n) ->
                 so (src_offset + size <= m) ->
                 RawMemory (MemoryChunk n) (MemoryChunk n) ()
     GetRawPtr : RawMemory (MemoryChunk n) (MemoryChunk n) (MemoryChunk n)

private
do_malloc : Nat -> IOExcept String Ptr
do_malloc size with (fromInteger (cast size) == size)
  | True  = do ptr <- ioe_lift $ mkForeign (FFun "malloc" [FInt] FPtr) (cast size)
               fail  <- ioe_lift $ nullPtr ptr
               if fail then ioe_fail "Cannot allocate memory"
               else return ptr
  | False = ioe_fail "The target architecture does not support adressing enough memory"

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
  = do b <- mkForeign (FFun "idris_peek" [FPtr, FInt] FInt) ptr (cast offset)
       bs <- do_peek ptr (S offset) n
       Prelude.Monad.return (Prelude.Vect.(::) (prim__intToB8 b) bs)

do_poke : Ptr -> Nat -> Vect Bits8 size -> IO ()
do_poke _   _      []     = return ()
do_poke ptr offset (b::bs)
  = do mkForeign (FFun "idris_poke" [FPtr, FInt, FAny Bits8] FUnit) ptr (cast offset) b
       do_poke ptr (S offset) bs

instance Handler RawMemory (IOExcept String) where
  handle () (Allocate n) k
    = do ptr <- do_malloc n
         k (CH ptr n) ()
  handle (CH ptr n) (Free) k
    = ioe_lift (do_free ptr) $> k () ()
  handle (CH ptr n) (Peek offset size _) k
    = do res <- ioe_lift (do_peek ptr offset size)
         k (CH ptr n) res
  handle (CH ptr n) (Poke offset content _) k
    = do ioe_lift (do_poke ptr offset content)
         k (CH ptr n) ()
  handle (CH dest_ptr n) (Move (CH src_ptr m) dest_offset src_offset size _ _) k
    = do ioe_lift (do_memmove dest_ptr src_ptr dest_offset src_offset size)
         k (CH dest_ptr n) ()
  handle (CH ptr n) (GetRawPtr) k
    = k (CH ptr n) (CH ptr n)

RAW_MEMORY : Type -> EFFECT
RAW_MEMORY t = MkEff t RawMemory

allocate : (n : Nat) -> EffM m [RAW_MEMORY ()] [RAW_MEMORY (MemoryChunk n)] ()
allocate size = Allocate size

free : EffM m [RAW_MEMORY (MemoryChunk n)] [RAW_MEMORY ()] ()
free = Free

peek : {n : Nat} ->
       (offset : Nat) ->
       (size : Nat) ->
       so (offset + size <= n) ->
       Eff m [RAW_MEMORY (MemoryChunk n)] (Vect Bits8 size)
peek offset size prf = Peek offset size prf

poke : {n : Nat} ->
       (offset : Nat) ->
       Vect Bits8 size ->
       so (offset + size <= n) ->
       Eff m [RAW_MEMORY (MemoryChunk n)] ()
poke offset content prf = Poke offset content prf

private
getRawPtr : Eff m [RAW_MEMORY (MemoryChunk n)] (MemoryChunk n)
getRawPtr = GetRawPtr

private
move' : {dst_size : Nat} ->
        {src_size : Nat} ->
        (src_ptr : MemoryChunk src_size) ->
        (dst_offset : Nat) ->
        (src_offset : Nat) ->
        (size : Nat) ->
        so (dst_offset + size <= dst_size) ->
        so (src_offset + size <= src_size) ->
        Eff m [RAW_MEMORY (MemoryChunk dst_size)] ()
move' src_ptr dst_offset src_offset size dst_bounds src_bounds
  = Move src_ptr dst_offset src_offset size dst_bounds src_bounds

data MoveDescriptor = Dst | Src

move : {dst_size : Nat} ->
       {src_size : Nat} ->
       (dst_offset : Nat) ->
       (src_offset : Nat) ->
       (size : Nat) ->
       so (dst_offset + size <= dst_size) ->
       so (src_offset + size <= src_size) ->
       Eff m [ Dst ::: RAW_MEMORY (MemoryChunk dst_size)
             , Src ::: RAW_MEMORY (MemoryChunk src_size)] ()
move dst_offset src_offset size dst_bounds src_bounds
  = do src_ptr <- Src :- getRawPtr
       Dst :- move' src_ptr dst_offset src_offset size dst_bounds src_bounds
       return ()
