module Effect.Memory

import Effects
import Control.IOExcept
import Data.Vect
import public Data.So

%access public export

export
data MemoryChunk : Nat -> Nat -> Type where
     CH : Ptr -> MemoryChunk size initialized

export
data RawMemory : Effect where
     Allocate   : (n : Nat) ->
                  RawMemory () () (\v => MemoryChunk n 0)
     Free       : RawMemory () (MemoryChunk n i) (\v => ())
     Initialize : Bits8 ->
                  (size : Nat) ->
                  So (i + size <= n) ->
                  RawMemory () (MemoryChunk n i) (\v => MemoryChunk n (i + size))
     Peek       : (offset : Nat) ->
                  (size : Nat) ->
                  So (offset + size <= i) ->
                  RawMemory (Vect size Bits8)
                            (MemoryChunk n i) (\v => MemoryChunk n i)
     Poke       :  (offset : Nat) ->
                  (Vect size Bits8) ->
                  So (offset <= i && offset + size <= n) ->
                  RawMemory () (MemoryChunk n i) (\v => MemoryChunk n (max i (offset + size)))
     Move       : (src : MemoryChunk src_size src_init) ->
                  (dst_offset : Nat) ->
                  (src_offset : Nat) ->
                  (size : Nat) ->
                  So (dst_offset <= dst_init && dst_offset + size <= dst_size) ->
                  So (src_offset + size <= src_init) ->
                  RawMemory () (MemoryChunk dst_size dst_init)
                            (\v => MemoryChunk dst_size (max dst_init (dst_offset + size)))
     GetRawPtr  : RawMemory (MemoryChunk n i) (MemoryChunk n i) (\v => MemoryChunk n i)

private
do_malloc : Nat -> IOExcept String Ptr
do_malloc size with (fromInteger (cast size) == size)
  | True  = do ptr <- ioe_lift $ foreign FFI_C "malloc" (Int -> IO Ptr) (fromInteger $ cast size)
               fail  <- ioe_lift $ nullPtr ptr
               if fail then ioe_fail "Cannot allocate memory"
               else pure ptr
  | False = ioe_fail "The target architecture does not support adressing enough memory"

private
do_memset : Ptr -> Nat -> Bits8 -> Nat -> IO ()
do_memset ptr offset c size
  = foreign FFI_C "idris_memset" (Ptr -> Int -> Bits8 -> Int -> IO ())
              ptr (fromInteger $ cast offset) c (fromInteger $ cast size)

private
do_free : Ptr -> IO ()
do_free ptr = foreign FFI_C "free" (Ptr -> IO ()) ptr

private
do_memmove : Ptr -> Ptr -> Nat -> Nat -> Nat -> IO ()
do_memmove dest src dest_offset src_offset size
  = foreign FFI_C "idris_memmove" (Ptr -> Ptr -> Int -> Int -> Int -> IO ())
       dest src (fromInteger $ cast dest_offset) (fromInteger $ cast src_offset) (fromInteger $ cast size)

private
do_peek : Ptr -> Nat -> (size : Nat) -> IO (Vect size Bits8)
do_peek _   _       Z = pure (Vect.Nil)
do_peek ptr offset (S n)
  = do b <- foreign FFI_C "idris_peek" (Ptr -> Int -> IO Bits8) ptr (fromInteger $ cast offset)
       bs <- do_peek ptr (S offset) n
       Applicative.pure (Vect.(::) b bs)

private
do_poke : Ptr -> Nat -> Vect size Bits8 -> IO ()
do_poke _   _      []     = pure ()
do_poke ptr offset (b::bs)
  = do foreign FFI_C "idris_poke" (Ptr -> Int -> Bits8 -> IO ()) ptr (fromInteger $ cast offset) b
       do_poke ptr (S offset) bs

implementation Handler RawMemory (IOExcept String) where
  handle () (Allocate n) k
    = do ptr <- do_malloc n
         k () (CH ptr)
  handle {-{res = MemoryChunk _ offset}-} (CH ptr) (Initialize {i} c size _) k
    = ioe_lift (do_memset ptr i c size) *> k () (CH ptr)
  handle (CH ptr) (Free) k
    = ioe_lift (do_free ptr) *> k () ()
  handle (CH ptr) (Peek offset size _) k
    = do res <- ioe_lift (do_peek ptr offset size)
         k res (CH ptr)
  handle (CH ptr) (Poke offset content _) k
    = do ioe_lift (do_poke ptr offset content)
         k () (CH ptr)
  handle (CH dest_ptr) (Move (CH src_ptr) dest_offset src_offset size _ _) k
    = do ioe_lift (do_memmove dest_ptr src_ptr dest_offset src_offset size)
         k () (CH dest_ptr)
  handle chunk (GetRawPtr) k
    = k chunk chunk

RAW_MEMORY : Type -> EFFECT
RAW_MEMORY t = MkEff t RawMemory

export
allocate : (n : Nat) ->
           Eff () [RAW_MEMORY ()] (\v => [RAW_MEMORY (MemoryChunk n 0)])
allocate size = call $ Allocate size

export
initialize : {i : Nat} ->
             {n : Nat} ->
             Bits8 ->
             (size : Nat) ->
             So (i + size <= n) ->
             Eff () [RAW_MEMORY (MemoryChunk n i)]
                       (\v => [RAW_MEMORY (MemoryChunk n (i + size))])
initialize c size prf = call $ Initialize c size prf

export
free : Eff () [RAW_MEMORY (MemoryChunk n i)] (\v => [RAW_MEMORY ()])
free = call Free

export
peek : {i : Nat} ->
       (offset : Nat) ->
       (size : Nat) ->
       So (offset + size <= i) ->
       { [RAW_MEMORY (MemoryChunk n i)] } Eff (Vect size Bits8)
peek offset size prf = call $ Peek offset size prf

export
poke : {n : Nat} ->
       {i : Nat} ->
       (offset : Nat) ->
       Vect size Bits8 ->
       So (offset <= i && offset + size <= n) ->
       Eff () [RAW_MEMORY (MemoryChunk n i)]
              (\v => [RAW_MEMORY (MemoryChunk n (max i (offset + size)))])
poke offset content prf = call $ Poke offset content prf

private
getRawPtr : { [RAW_MEMORY (MemoryChunk n i)] } Eff (MemoryChunk n i)
getRawPtr = call $ GetRawPtr

private
move' : {dst_size : Nat} ->
        {dst_init : Nat} ->
        {src_init : Nat} ->
        (src_ptr : MemoryChunk src_size src_init) ->
        (dst_offset : Nat) ->
        (src_offset : Nat) ->
        (size : Nat) ->
        So (dst_offset <= dst_init && dst_offset + size <= dst_size) ->
        So (src_offset + size <= src_init) ->
        Eff () [RAW_MEMORY (MemoryChunk dst_size dst_init)]
               (\v => [RAW_MEMORY (MemoryChunk dst_size (max dst_init (dst_offset + size)))])
move' src_ptr dst_offset src_offset size dst_bounds src_bounds
  = call $ Move src_ptr dst_offset src_offset size dst_bounds src_bounds

data MoveDescriptor = Dst | Src

export
move : {dst_size : Nat} ->
       {dst_init : Nat} ->
       {src_size : Nat} ->
       {src_init : Nat} ->
       (dst_offset : Nat) ->
       (src_offset : Nat) ->
       (size : Nat) ->
       So (dst_offset <= dst_init && dst_offset + size <= dst_size) ->
       So (src_offset + size <= src_init) ->
       Eff ()
              [ Dst ::: RAW_MEMORY (MemoryChunk dst_size dst_init)
              , Src ::: RAW_MEMORY (MemoryChunk src_size src_init)]
              (\v =>
                [ Dst ::: RAW_MEMORY (MemoryChunk dst_size (max dst_init (dst_offset + size)))
                , Src ::: RAW_MEMORY (MemoryChunk src_size src_init)])
move dst_offset src_offset size dst_bounds src_bounds
  = do src_ptr <- Src :- getRawPtr
       Dst :- move' src_ptr dst_offset src_offset size dst_bounds src_bounds
       pure ()

