module Prelude

import public Builtins
import public IO

import public Prelude.Algebra
import public Prelude.Basics
import public Prelude.Bool
import public Prelude.Classes
import public Prelude.Cast
import public Prelude.Nat
import public Prelude.List
import public Prelude.Maybe
import public Prelude.Monad
import public Prelude.Applicative
import public Prelude.Foldable
import public Prelude.Functor
import public Prelude.Either
import public Prelude.Strings
import public Prelude.Chars
import public Prelude.Traversable
import public Prelude.Bits
import public Prelude.Uninhabited
import public Prelude.Pairs
import public Prelude.Stream
import public Prelude.Providers
import public Decidable.Equality
import public Language.Reflection
import public Language.Reflection.Errors

%access public
%default total

-- Show and instances

class Show a where
    partial show : a -> String

instance Show Int where
    show = prim__toStrInt

instance Show Integer where
    show = prim__toStrBigInt

instance Show Float where
    show = prim__floatToStr


firstCharIs : (Char -> Bool) -> String -> Bool
firstCharIs p s with (strM s)
  firstCharIs p ""             | StrNil = False
  firstCharIs p (strCons c cs) | StrCons c cs = p c

protectEsc : (Char -> Bool) -> String -> String -> String
protectEsc p f s = f ++ (if firstCharIs p s then "\\&" else "") ++ s

showLitChar : Char -> String -> String
showLitChar '\a'   = ("\\a" ++)
showLitChar '\b'   = ("\\b" ++)
showLitChar '\f'   = ("\\f" ++)
showLitChar '\n'   = ("\\n" ++)
showLitChar '\r'   = ("\\r" ++)
showLitChar '\t'   = ("\\t" ++)
showLitChar '\v'   = ("\\v" ++)
showLitChar '\SO'  = protectEsc (== 'H') "\\SO"
showLitChar '\DEL' = ("\\DEL" ++)
showLitChar '\\'   = ("\\\\" ++)
showLitChar c      = case getAt (cast (cast {to=Int} c)) asciiTab of
                          Just k => strCons '\\' . (k ++)
                          Nothing => if (c > '\DEL')
                                        then strCons '\\' . protectEsc isDigit (show (cast {to=Int} c))
                                        else strCons c
  where asciiTab : List String
        asciiTab = ["NUL", "SOH", "STX", "ETX", "EOT", "ENQ", "ACK", "BEL",
                    "BS",  "HT",  "LF",  "VT",  "FF",  "CR",  "SO",  "SI",
                    "DLE", "DC1", "DC2", "DC3", "DC4", "NAK", "SYN", "ETB",
                    "CAN", "EM",  "SUB", "ESC", "FS",  "GS",  "RS",  "US"]

        getAt : Nat -> List String -> Maybe String
        getAt Z     (x :: xs) = Just x
        getAt (S k) (x :: xs) = getAt k xs
        getAt _     []        = Nothing

showLitString : List Char -> String -> String
showLitString []        = id
showLitString ('"'::cs) = ("\\\"" ++) . showLitString cs
showLitString (c  ::cs) = showLitChar c . showLitString cs

instance Show Char where
  show '\'' = "'\\''"
  show c    = strCons '\'' (showLitChar c "'")

instance Show String where
  show cs = strCons '"' (showLitString (cast cs) "\"")

instance Show Nat where
    show n = show (the Integer (cast n))

instance Show Bool where
    show True = "True"
    show False = "False"

instance Show () where
  show () = "()"

instance Show Bits8 where
  show b = b8ToString b

instance Show Bits16 where
  show b = b16ToString b

instance Show Bits32 where
  show b = b32ToString b

instance Show Bits64 where
  show b = b64ToString b

instance (Show a, Show b) => Show (a, b) where
    show (x, y) = "(" ++ show x ++ ", " ++ show y ++ ")"

instance Show a => Show (List a) where
    show xs = "[" ++ show' "" xs ++ "]" where
        show' acc []        = acc
        show' acc [x]       = acc ++ show x
        show' acc (x :: xs) = show' (acc ++ show x ++ ", ") xs

instance Show a => Show (Maybe a) where
    show Nothing = "Nothing"
    show (Just x) = "Just " ++ show x

---- Functor instances

instance Functor PrimIO where
    map f io = prim_io_bind io (prim_io_return . f)

instance Functor (IO' ffi) where
    map f io = io_bind io (\b => io_return (f b))

instance Functor Maybe where
    map f (Just x) = Just (f x)
    map f Nothing  = Nothing

instance Functor (Either e) where
    map f (Left l) = Left l
    map f (Right r) = Right (f r)

---- Applicative instances

instance Applicative PrimIO where
    pure = prim_io_return

    am <*> bm = prim_io_bind am (\f => prim_io_bind bm (prim_io_return . f))

instance Applicative (IO' ffi) where
    pure x = io_return x
    f <*> a = io_bind f (\f' =>
                io_bind a (\a' =>
                  io_return (f' a')))

instance Applicative Maybe where
    pure = Just

    (Just f) <*> (Just a) = Just (f a)
    _        <*> _        = Nothing

instance Applicative (Either e) where
    pure = Right

    (Left a) <*> _          = Left a
    (Right f) <*> (Right r) = Right (f r)
    (Right _) <*> (Left l)  = Left l

instance Applicative List where
    pure x = [x]

    fs <*> vs = concatMap (\f => map f vs) fs

---- Alternative instances

instance Alternative Maybe where
    empty = Nothing

    (Just x) <|> _ = Just x
    Nothing  <|> v = v

instance Alternative List where
    empty = []

    (<|>) = (++)

---- Monad instances

instance Monad PrimIO where
    b >>= k = prim_io_bind b k

instance Monad (IO' ffi) where
    b >>= k = io_bind b k

instance Monad Maybe where
    Nothing  >>= k = Nothing
    (Just x) >>= k = k x

instance Monad (Either e) where
    (Left n) >>= _ = Left n
    (Right r) >>= f = f r

instance Monad List where
    m >>= f = concatMap f m

---- Traversable instances

instance Traversable Maybe where
    traverse f Nothing = pure Nothing
    traverse f (Just x) = [| Just (f x) |]

instance Traversable List where
    traverse f [] = pure List.Nil
    traverse f (x::xs) = [| List.(::) (f x) (traverse f xs) |]

---- some mathematical operations
---- XXX this should probably go some place else,
pow : (Num a) => a -> Nat -> a
pow x Z = 1
pow x (S n) = x * (pow x n)

---- Ranges

natRange : Nat -> List Nat
natRange n = List.reverse (go n)
  where go Z = []
        go (S n) = n :: go n

-- predefine Nat versions of Enum, so we can use them in the default impls
total natEnumFromThen : Nat -> Nat -> Stream Nat
natEnumFromThen n inc = n :: natEnumFromThen (inc + n) inc
total natEnumFromTo : Nat -> Nat -> List Nat
natEnumFromTo n m = map (plus n) (natRange ((S m) - n))
total natEnumFromThenTo : Nat -> Nat -> Nat -> List Nat
natEnumFromThenTo _ Z   _ = []
natEnumFromThenTo n inc m = map (plus n . (* inc)) (natRange (S ((m - n) `div` inc)))

class Enum a where
  total pred : a -> a
  total succ : a -> a
  succ e = fromNat (S (toNat e))
  total toNat : a -> Nat
  total fromNat : Nat -> a
  total enumFrom : a -> Stream a
  enumFrom n = n :: enumFrom (succ n)
  total enumFromThen : a -> a -> Stream a
  enumFromThen x y = map fromNat (natEnumFromThen (toNat x) (toNat y))
  total enumFromTo : a -> a -> List a
  enumFromTo x y = map fromNat (natEnumFromTo (toNat x) (toNat y))
  total enumFromThenTo : a -> a -> a -> List a
  enumFromThenTo x1 x2 y = map fromNat (natEnumFromThenTo (toNat x1) (toNat x2) (toNat y))

instance Enum Nat where
  pred n = Nat.pred n
  succ n = S n
  toNat x = id x
  fromNat x = id x
  enumFromThen x y = natEnumFromThen x y
  enumFromThenTo x y z = natEnumFromThenTo x y z
  enumFromTo x y = natEnumFromTo x y

instance Enum Integer where
  pred n = n - 1
  succ n = n + 1
  toNat n = cast n
  fromNat n = cast n
  enumFromThen n inc = n :: enumFromThen (inc + n) inc
  enumFromTo n m = if n <= m
                   then go (natRange (S (cast {to = Nat} (m - n))))
                   else []
    where go : List Nat -> List Integer
          go [] = []
          go (x :: xs) = n + cast x :: go xs
  enumFromThenTo _ 0   _ = []
  enumFromThenTo n inc m = go (natRange (S (fromInteger (abs (m - n)) `div` fromInteger (abs inc))))
    where go : List Nat -> List Integer
          go [] = []
          go (x :: xs) = n + (cast x * inc) :: go xs

instance Enum Int where
  pred n = n - 1
  succ n = n + 1
  toNat n = cast n
  fromNat n = cast n
  enumFromTo n m =
    if n <= m
       then go [] (cast {to = Nat} (m - n)) m
       else []
       where
         go : List Int -> Nat -> Int -> List Int
         go acc Z     m = m :: acc
         go acc (S k) m = go (m :: acc) k (m - 1)
  enumFromThen n inc = n :: enumFromThen (inc + n) inc
  enumFromThenTo _ 0   _ = []
  enumFromThenTo n inc m = go (natRange (S (cast {to=Nat} (abs (m - n)) `div` cast {to=Nat} (abs inc))))
    where go : List Nat -> List Int
          go [] = []
          go (x :: xs) = n + (cast x * inc) :: go xs

syntax "[" [start] ".." [end] "]"
     = enumFromTo start end
syntax "[" [start] "," [next] ".." [end] "]"
     = enumFromThenTo start (next - start) end

syntax "[" [start] ".." "]"
     = enumFrom start
syntax "[" [start] "," [next] ".." "]"
     = enumFromThen start (next - start)

---- More utilities

curry : ((a, b) -> c) -> a -> b -> c
curry f a b = f (a, b)

uncurry : (a -> b -> c) -> (a, b) -> c
uncurry f (a, b) = f a b

---- some basic io

||| Output a string to stdout without a trailing newline
putStr : String -> IO' ffi ()
putStr x = do prim_write x
              return ()

||| Output a string to stdout with a trailing newline
putStrLn : String -> IO' ffi ()
putStrLn x = putStr (x ++ "\n")

||| Output something showable to stdout, without a trailing newline
partial
print : Show a => a -> IO' ffi ()
print x = putStr (show x)

||| Output something showable to stdout, with a trailing newline
partial
printLn : Show a => a -> IO' ffi ()
printLn x = putStrLn (show x)

||| Read one line of input from stdin
partial
getLine : IO' ffi String
getLine = prim_read

||| Write a single character to stdout
partial
putChar : Char -> IO ()
putChar c = foreign FFI_C "putchar" (Int -> IO ()) (cast c)

||| Write a singel character to stdout, with a trailing newline
partial
putCharLn : Char -> IO ()
putCharLn c = putStrLn (singleton c)

||| Read a single character from stdin
partial
getChar : IO Char
getChar = map cast $ foreign FFI_C "getchar" (IO Int)

---- some basic file handling

||| A file handle
abstract
data File = FHandle Ptr

||| Standard input
stdin : File
stdin = FHandle prim__stdin

||| Standard output
stdout : File
stdout = FHandle prim__stdout

||| Standard output
stderr : File
stderr = FHandle prim__stderr

||| Call the RTS's file opening function
do_fopen : String -> String -> IO Ptr
do_fopen f m
   = foreign FFI_C "fileOpen" (String -> String -> IO Ptr) f m

||| Open a file
||| @ f the filename
||| @ m the mode as a String (`"r"`, `"w"`, or `"r+"`)
fopen : (f : String) -> (m : String) -> IO File
fopen f m = do h <- do_fopen f m
               return (FHandle h)

||| Modes for opening files
data Mode = Read | Write | ReadWrite

||| Open a file
||| @ f the filename
||| @ m the mode
partial
openFile : (f : String) -> (m : Mode) -> IO File
openFile f m = fopen f (modeStr m) where
  modeStr Read  = "r"
  modeStr Write = "w"
  modeStr ReadWrite = "r+"

partial
do_fclose : Ptr -> IO ()
do_fclose h = foreign FFI_C "fileClose" (Ptr -> IO ()) h

partial
closeFile : File -> IO ()
closeFile (FHandle h) = do_fclose h

partial
do_fread : Ptr -> IO' l String
do_fread h = prim_fread h

fgetc : File -> IO Char
fgetc (FHandle h) = return (cast !(foreign FFI_C "fgetc" (Ptr -> IO Int) h))

fgetc' : File -> IO (Maybe Char)
fgetc' (FHandle h)
   = do x <- foreign FFI_C "fgetc" (Ptr -> IO Int) h
        if (x < 0) then return Nothing
                   else return (Just (cast x))

fflush : File -> IO ()
fflush (FHandle h) = foreign FFI_C "fflush" (Ptr -> IO ()) h

do_popen : String -> String -> IO Ptr
do_popen f m = foreign FFI_C "do_popen" (String -> String -> IO Ptr) f m

popen : String -> Mode -> IO File
popen f m = do ptr <- do_popen f (modeStr m)
               return (FHandle ptr)
  where
    modeStr Read  = "r"
    modeStr Write = "w"
    modeStr ReadWrite = "r+"

pclose : File -> IO ()
pclose (FHandle h) = foreign FFI_C "pclose" (Ptr -> IO ()) h

-- mkForeign (FFun "idris_readStr" [FPtr, FPtr] (FAny String))
--                        prim__vm h

partial
fread : File -> IO' l String
fread (FHandle h) = do_fread h

partial
do_fwrite : Ptr -> String -> IO ()
do_fwrite h s = do prim_fwrite h s
                   return ()

partial
fwrite : File -> String -> IO ()
fwrite (FHandle h) s = do_fwrite h s

partial
do_feof : Ptr -> IO Int
do_feof h = foreign FFI_C "fileEOF" (Ptr -> IO Int) h

||| Check if a file handle has reached the end
feof : File -> IO Bool
feof (FHandle h) = do eof <- do_feof h
                      return (not (eof == 0))

partial
do_ferror : Ptr -> IO Int
do_ferror h = foreign FFI_C "fileError" (Ptr -> IO Int) h

ferror : File -> IO Bool
ferror (FHandle h) = do err <- do_ferror h
                        return (not (err == 0))

fpoll : File -> IO Bool
fpoll (FHandle h) = do p <- foreign FFI_C "fpoll" (Ptr -> IO Int) h
                       return (p > 0)

||| Check if a foreign pointer is null
partial
nullPtr : Ptr -> IO Bool
nullPtr p = do ok <- foreign FFI_C "isNull" (Ptr -> IO Int) p
               return (ok /= 0)

||| Check if a supposed string was actually a null pointer
partial
nullStr : String -> IO Bool
nullStr p = do ok <- foreign FFI_C "isNull" (String -> IO Int) p
               return (ok /= 0)

namespace JSNull
  ||| Check if a foreign pointer is null
  partial
  nullPtr : Ptr -> JS_IO Bool
  nullPtr p = do ok <- foreign FFI_JS "isNull" (Ptr -> JS_IO Int) p
                 return (ok /= 0)

  ||| Check if a supposed string was actually a null pointer
  partial
  nullStr : String -> JS_IO Bool
  nullStr p = do ok <- foreign FFI_JS "isNull" (String -> JS_IO Int) p
                 return (ok /= 0)


||| Pointer equality
eqPtr : Ptr -> Ptr -> IO Bool
eqPtr x y = do eq <- foreign FFI_C "idris_eqPtr" (Ptr -> Ptr -> IO Int) x y
               return (eq /= 0)

||| Check whether a file handle is actually a null pointer
partial
validFile : File -> IO Bool
validFile (FHandle h) = do x <- nullPtr h
                           return (not x)

||| Loop while some test is true
|||
||| @ test the condition of the loop
||| @ body the loop body
partial -- obviously
while : (test : IO Bool) -> (body : IO ()) -> IO ()
while t b = do v <- t
               if v then do b
                            while t b
                    else return ()

||| Read the contents of a file into a string
partial -- no error checking!
readFile : String -> IO String
readFile fn = do h <- openFile fn Read
                 c <- readFile' h ""
                 closeFile h
                 return c
  where
    partial
    readFile' : File -> String -> IO String
    readFile' h contents =
       do x <- feof h
          if not x then do l <- fread h
                           readFile' h (contents ++ l)
                   else return contents
