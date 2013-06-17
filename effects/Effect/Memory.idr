module Effect.Memory

import Effects
import Effect.File
import Control.IOExcept
import Decidable.Order

%access public

data MemoryType = Ram | Mapped

abstract
data MemoryChunk : MemoryType -> Mode -> Nat -> Nat -> Type where
     CH : Ptr -> MemoryChunk t mode size initialized

abstract
data RawMemory : Effect where
     Allocate   : (n : Nat) ->
                  RawMemory () (MemoryChunk Ram ReadWrite n 0) ()
     MMap       : AllowsRead mode =>
                  (handle : File) ->
                  RawMemory () (MemoryChunk Mapped mode n n) ()
     Free       : RawMemory (MemoryChunk t mode n i) () ()
     Initialize : AllowsWrite mode =>
                  Bits8 ->
                  (size : Nat) ->
                  Given (natLTE (i + size) n) ->
                  RawMemory (MemoryChunk t mode n i) (MemoryChunk t mode n (i + size)) ()
     Peek       : AllowsRead mode =>
                  (offset : Nat) ->
                  (size : Nat) ->
                  Given (natLTE (offset + size) i) ->
                  RawMemory (MemoryChunk t mode n i) (MemoryChunk t mode n i) (Vect Bits8 size)
     Poke       : AllowsWrite mode =>
                  (offset : Nat) ->
                  (Vect Bits8 size) ->
                  Given (natLTE offset i) ->
                  Given (natLTE (offset + size) n) ->
                  RawMemory (MemoryChunk t mode n i) (MemoryChunk t mode n (max i (offset + size))) ()
     Move       : (AllowsWrite mode, AllowsRead mode') =>
                  (src : MemoryChunk t' mode' src_size src_init) ->
                  (dst_offset : Nat) ->
                  (src_offset : Nat) ->
                  (size : Nat) ->
                  Given (natLTE dst_offset dst_init) ->
                  Given (natLTE (dst_offset + size) dst_size) ->
                  Given (natLTE (src_offset + size) src_init) ->
                  RawMemory (MemoryChunk t mode dst_size dst_init)
                            (MemoryChunk t mode dst_size (max dst_init (dst_offset + size))) ()
     GetRawPtr  : RawMemory (MemoryChunk t mode n i) (MemoryChunk t mode n i) (MemoryChunk t mode n i)

private
do_malloc : Nat -> IOExcept String Ptr
do_malloc size with (fromInteger (cast size) == size)
  | True  = do ptr  <- ioe_lift $ mkForeign (FFun "malloc" [FInt] FPtr) (cast size)
               fail <- ioe_lift $ nullPtr ptr
               if fail then ioe_fail "Cannot allocate memory"
               else return ptr
  | False = ioe_fail "The target architecture does not support adressing enough memory"

private
do_mmap : File -> Mode -> Nat -> IOExcept String Ptr
do_mmap (FHandle ptr) mode size with (fromInteger (cast size) == size)
  | True  = do res  <- ioe_lift $ mkForeign (FFun "idris_mmap" [FPtr, FInt, FInt] FPtr)
                                            ptr (case mode of Read => 0; _ => 1) (cast size)
               fail <- ioe_lift $ nullPtr ptr
               if fail then ioe_fail "Cannot map file"
               else return res             
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
do_munmap : Ptr -> Nat -> IOExcept String ()
do_munmap ptr size
  = do res <- ioe_lift $ mkForeign (FFun "idris_munmap" [FPtr, FInt] FInt)
                                   ptr (cast size)
       if (res == 0) then return ()
       else ioe_fail "Could not unmap memory"

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
  handle {res' = MemoryChunk Mapped mode n _} () (MMap h) k
    = do ptr <- do_mmap h mode n
         k (CH ptr) ()
  handle {res = MemoryChunk _ _ _ offset} (CH ptr) (Initialize c size _) k
    = ioe_lift (do_memset ptr offset c size) $> k (CH ptr) ()
  handle {res = MemoryChunk Ram _ _ _} (CH ptr) (Free) k
    = ioe_lift (do_free ptr) $> k () ()
  handle {res = MemoryChunk Mapped _ size _} (CH ptr) (Free) k
    = do_munmap ptr size $> k () ()
  handle (CH ptr) (Peek offset size _) k
    = do res <- ioe_lift (do_peek ptr offset size)
         k (CH ptr) res
  handle (CH ptr) (Poke offset content _ _) k
    = do ioe_lift (do_poke ptr offset content)
         k (CH ptr) ()
  handle (CH dest_ptr) (Move (CH src_ptr) dest_offset src_offset size _ _ _) k
    = do ioe_lift (do_memmove dest_ptr src_ptr dest_offset src_offset size)
         k (CH dest_ptr) ()
  handle chunk (GetRawPtr) k
    = k chunk chunk

RAW_MEMORY : Type -> EFFECT
RAW_MEMORY t = MkEff t RawMemory

allocate : (Handler RawMemory m) =>
           (n : Nat) ->
           EffM m [RAW_MEMORY ()] [RAW_MEMORY (MemoryChunk Ram ReadWrite n 0)] ()
allocate size = Allocate size


data Role = Disk | Mem

mmap : (Handler FileIO m, Handler RawMemory m, AllowsRead mode) =>
       (n : Nat) ->
       EffM m [ Disk ::: FILE_IO (OpenFile mode) 
              , Mem ::: RAW_MEMORY () ] 
              [ Disk ::: FILE_IO (OpenFile mode)
              , Mem ::: RAW_MEMORY (MemoryChunk Mapped mode n n) ] ()
mmap size = do h <- Disk :- getHandle
               Mem :- effect' (MMap h)

initialize : (Handler RawMemory m, AllowsWrite mode) =>
             {i : Nat} ->
             {n : Nat} ->
             Bits8 ->
             (size : Nat) ->
             Given (natLTE (i + size) n) ->
             EffM m [RAW_MEMORY (MemoryChunk t mode n i)]
                    [RAW_MEMORY (MemoryChunk t mode n (i + size))] ()
initialize c size prf = Initialize c size prf

free : (Handler RawMemory m) =>
       EffM m [RAW_MEMORY (MemoryChunk t mode n i)] [RAW_MEMORY ()] ()
free = Free

peek : (Handler RawMemory m, AllowsRead mode) =>
       {i : Nat} ->
       (offset : Nat) ->
       (size : Nat) ->
       Given (natLTE (offset + size) i) ->
       Eff m [RAW_MEMORY (MemoryChunk t mode n i)] (Vect Bits8 size)
peek offset size prf = Peek offset size prf

poke : (Handler RawMemory m, AllowsWrite mode) =>
       {n : Nat} ->
       {i : Nat} ->
       (offset : Nat) ->
       Vect Bits8 size ->
       Given (natLTE offset i) ->
       Given (natLTE (offset + size) n) ->
       EffM m [RAW_MEMORY (MemoryChunk t mode n i)]
              [RAW_MEMORY (MemoryChunk t mode n (max i (offset + size)))] ()
poke offset content prf_init prf = Poke offset content prf_init prf

private
getRawPtr : (Handler RawMemory m) =>
            Eff m [RAW_MEMORY (MemoryChunk t mode n i)] (MemoryChunk t mode n i)
getRawPtr = GetRawPtr

private
move' : (Handler RawMemory m, AllowsWrite mode, AllowsRead mode') =>
        {dst_size : Nat} ->
        {dst_init : Nat} ->
        {src_init : Nat} ->
        (src_ptr : MemoryChunk t' mode' src_size src_init) ->
        (dst_offset : Nat) ->
        (src_offset : Nat) ->
        (size : Nat) ->
        Given (natLTE dst_offset dst_init) ->
        Given (natLTE (dst_offset + size) dst_size) ->
        Given (natLTE (src_offset + size) src_init) ->
        EffM m [RAW_MEMORY (MemoryChunk t mode dst_size dst_init)]
               [RAW_MEMORY (MemoryChunk t mode dst_size (max dst_init (dst_offset + size)))] ()
move' src_ptr dst_offset src_offset size dst_bounds_init dst_bounds src_bounds
  = Move src_ptr dst_offset src_offset size dst_bounds_init dst_bounds src_bounds

data MoveDescriptor = Dst | Src

move : (Handler RawMemory m, AllowsWrite mode, AllowsRead mode') =>
       {dst_size : Nat} ->
       {dst_init : Nat} ->
       {src_size : Nat} ->
       {src_init : Nat} ->
       (dst_offset : Nat) ->
       (src_offset : Nat) ->
       (size : Nat) ->
       Given (natLTE dst_offset dst_init) ->
       Given (natLTE (dst_offset + size) dst_size) ->
       Given (natLTE (src_offset + size) src_init) ->
       EffM m [ Dst ::: RAW_MEMORY (MemoryChunk t mode dst_size dst_init)
              , Src ::: RAW_MEMORY (MemoryChunk t' mode' src_size src_init)]
              [ Dst ::: RAW_MEMORY (MemoryChunk t mode dst_size (max dst_init (dst_offset + size)))
              , Src ::: RAW_MEMORY (MemoryChunk t' mode' src_size src_init)] ()
move dst_offset src_offset size dst_bounds_init dst_bounds src_bounds
  = do src_ptr <- Src :- getRawPtr
       Dst :- move' src_ptr dst_offset src_offset size dst_bounds_init dst_bounds src_bounds
       return ()
