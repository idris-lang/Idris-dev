module Prelude

import Builtins
import IO

import Prelude.Bool
import Prelude.Classes
import Prelude.Cast
import Prelude.Nat
import Prelude.Fin
import Prelude.List
import Prelude.Maybe
import Prelude.Monad
import Prelude.Applicative
import Prelude.Functor
import Prelude.Either
import Prelude.Vect
import Prelude.Strings
import Prelude.Chars
import Prelude.Traversable
import Prelude.Bits
import Prelude.Stream

import Decidable.Equality

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

asciiTab : Vect 32 String
asciiTab = ["NUL", "SOH", "STX", "ETX", "EOT", "ENQ", "ACK", "BEL",
            "BS",  "HT",  "LF",  "VT",  "FF",  "CR",  "SO",  "SI",
            "DLE", "DC1", "DC2", "DC3", "DC4", "NAK", "SYN", "ETB",
            "CAN", "EM",  "SUB", "ESC", "FS",  "GS",  "RS",  "US"]

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
showLitChar c      = case (integerToFin (cast (cast {to=Int} c)) 32) of
                          Just k => strCons '\\' . ((index k asciiTab) ++)
                          Nothing => if (c > '\DEL')
                                        then strCons '\\' . protectEsc isDigit (show (cast {to=Int} c))
                                        else strCons c

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

%assert_total
viewB8x16 : Bits8x16 -> (Bits8, Bits8, Bits8, Bits8, Bits8, Bits8, Bits8, Bits8, Bits8, Bits8, Bits8, Bits8, Bits8, Bits8, Bits8, Bits8)
viewB8x16 x = ( prim__indexB8x16 x (prim__truncBigInt_B32 0)
              , prim__indexB8x16 x (prim__truncBigInt_B32 1)
              , prim__indexB8x16 x (prim__truncBigInt_B32 2)
              , prim__indexB8x16 x (prim__truncBigInt_B32 3)
              , prim__indexB8x16 x (prim__truncBigInt_B32 4)
              , prim__indexB8x16 x (prim__truncBigInt_B32 5)
              , prim__indexB8x16 x (prim__truncBigInt_B32 6)
              , prim__indexB8x16 x (prim__truncBigInt_B32 7)
              , prim__indexB8x16 x (prim__truncBigInt_B32 8)
              , prim__indexB8x16 x (prim__truncBigInt_B32 9)
              , prim__indexB8x16 x (prim__truncBigInt_B32 10)
              , prim__indexB8x16 x (prim__truncBigInt_B32 11)
              , prim__indexB8x16 x (prim__truncBigInt_B32 12)
              , prim__indexB8x16 x (prim__truncBigInt_B32 13)
              , prim__indexB8x16 x (prim__truncBigInt_B32 14)
              , prim__indexB8x16 x (prim__truncBigInt_B32 15)
              )

instance Show Bits8x16 where
  show x =
    case viewB8x16 x of
      (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p) =>
        "<" ++ prim__toStrB8 a
        ++ ", " ++ prim__toStrB8 b
        ++ ", " ++ prim__toStrB8 c
        ++ ", " ++ prim__toStrB8 d
        ++ ", " ++ prim__toStrB8 e
        ++ ", " ++ prim__toStrB8 f
        ++ ", " ++ prim__toStrB8 g
        ++ ", " ++ prim__toStrB8 h
        ++ ", " ++ prim__toStrB8 i
        ++ ", " ++ prim__toStrB8 j
        ++ ", " ++ prim__toStrB8 k
        ++ ", " ++ prim__toStrB8 l
        ++ ", " ++ prim__toStrB8 m
        ++ ", " ++ prim__toStrB8 n
        ++ ", " ++ prim__toStrB8 o
        ++ ", " ++ prim__toStrB8 p
        ++ ">"

%assert_total
viewB16x8 : Bits16x8 -> (Bits16, Bits16, Bits16, Bits16, Bits16, Bits16, Bits16, Bits16)
viewB16x8 x = ( prim__indexB16x8 x (prim__truncBigInt_B32 0)
              , prim__indexB16x8 x (prim__truncBigInt_B32 1)
              , prim__indexB16x8 x (prim__truncBigInt_B32 2)
              , prim__indexB16x8 x (prim__truncBigInt_B32 3)
              , prim__indexB16x8 x (prim__truncBigInt_B32 4)
              , prim__indexB16x8 x (prim__truncBigInt_B32 5)
              , prim__indexB16x8 x (prim__truncBigInt_B32 6)
              , prim__indexB16x8 x (prim__truncBigInt_B32 7)
              )

instance Show Bits16x8 where
  show x =
    case viewB16x8 x of
      (a, b, c, d, e, f, g, h) =>
        "<" ++ prim__toStrB16 a
        ++ ", " ++ prim__toStrB16 b
        ++ ", " ++ prim__toStrB16 c
        ++ ", " ++ prim__toStrB16 d
        ++ ", " ++ prim__toStrB16 e
        ++ ", " ++ prim__toStrB16 f
        ++ ", " ++ prim__toStrB16 g
        ++ ", " ++ prim__toStrB16 h
        ++ ">"

%assert_total
viewB32x4 : Bits32x4 -> (Bits32, Bits32, Bits32, Bits32)
viewB32x4 x = ( prim__indexB32x4 x (prim__truncBigInt_B32 0)
              , prim__indexB32x4 x (prim__truncBigInt_B32 1)
              , prim__indexB32x4 x (prim__truncBigInt_B32 2)
              , prim__indexB32x4 x (prim__truncBigInt_B32 3)
              )

instance Show Bits32x4 where
  show x =
    case viewB32x4 x of
      (a, b, c, d) =>
        "<" ++ prim__toStrB32 a
        ++ ", " ++ prim__toStrB32 b
        ++ ", " ++ prim__toStrB32 c
        ++ ", " ++ prim__toStrB32 d
        ++ ">"

%assert_total
viewB64x2 : Bits64x2 -> (Bits64, Bits64)
viewB64x2 x = ( prim__indexB64x2 x (prim__truncBigInt_B32 0)
              , prim__indexB64x2 x (prim__truncBigInt_B32 1)
              )

instance Show Bits64x2 where
  show x =
    case viewB64x2 x of
      (a, b) =>
        "<" ++ prim__toStrB64 a
        ++ ", " ++ prim__toStrB64 b
        ++ ">"

instance (Show a, Show b) => Show (a, b) where
    show (x, y) = "(" ++ show x ++ ", " ++ show y ++ ")"

instance Show a => Show (List a) where
    show xs = "[" ++ show' "" xs ++ "]" where
        show' acc []        = acc
        show' acc [x]       = acc ++ show x
        show' acc (x :: xs) = show' (acc ++ show x ++ ", ") xs

instance Show a => Show (Vect n a) where
    show xs = "[" ++ show' xs ++ "]" where
        show' : Vect n a -> String
        show' []        = ""
        show' [x]       = show x
        show' (x :: xs) = show x ++ ", " ++ show' xs

instance Show a => Show (Maybe a) where
    show Nothing = "Nothing"
    show (Just x) = "Just " ++ show x

---- Functor instances

instance Functor PrimIO where
    map f io = prim_io_bind io (prim_io_return . f)

instance Functor IO where
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

    am <$> bm = prim_io_bind am (\f => prim_io_bind bm (prim_io_return . f))

instance Applicative IO where
    pure x = io_return x
    f <$> a = io_bind f (\f' =>
                io_bind a (\a' =>
                  io_return (f' a')))

instance Applicative Maybe where
    pure = Just

    (Just f) <$> (Just a) = Just (f a)
    _        <$> _        = Nothing

instance Applicative (Either e) where
    pure = Right

    (Left a) <$> _          = Left a
    (Right f) <$> (Right r) = Right (f r)
    (Right _) <$> (Left l)  = Left l

instance Applicative List where
    pure x = [x]

    fs <$> vs = concatMap (\f => map f vs) fs

instance Applicative (Vect k) where
    pure = replicate _

    fs <$> vs = zipWith apply fs vs

instance Applicative Stream where
  pure = repeat
  (<$>) = zipWith apply

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

instance Monad IO where
    b >>= k = io_bind b k

instance Monad Maybe where
    Nothing  >>= k = Nothing
    (Just x) >>= k = k x

instance Monad (Either e) where
    (Left n) >>= _ = Left n
    (Right r) >>= f = f r

instance Monad List where
    m >>= f = concatMap f m

instance Monad (Vect n) where
    m >>= f = diag (map f m)

instance Monad Stream where
  s >>= f = diag (map f s)

---- Traversable instances

instance Traversable Maybe where
    traverse f Nothing = pure Nothing
    traverse f (Just x) = [| Just (f x) |]

instance Traversable List where
    traverse f [] = pure List.Nil
    traverse f (x::xs) = [| List.(::) (f x) (traverse f xs) |]

instance Traversable (Vect n) where
    traverse f [] = pure Vect.Nil
    traverse f (x::xs) = [| Vect.(::) (f x) (traverse f xs) |]

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

class Enum a where
  total pred : a -> a
  total succ : a -> a
  total toNat : a -> Nat
  total fromNat : Nat -> a
  total enumFrom : a -> Stream a
  enumFrom n = n :: enumFrom (succ n)
  total enumFromThen : a -> a -> Stream a
  total enumFromTo : a -> a -> List a
  total enumFromThenTo : a -> a -> a -> List a


instance Enum Nat where
  pred = Nat.pred
  succ = S
  toNat = id
  fromNat = id
  enumFromThen n inc = n :: enumFromThen (fromNat (plus (toNat inc) (toNat n))) inc
  enumFromThenTo _ Z   _ = []
  enumFromThenTo n inc m = map (plus n . (* inc)) (natRange (S ((m - n) `div` inc)))
  enumFromTo n m = map (plus n) (natRange ((S m) - n))

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
  enumFromThen n inc = n :: enumFromThen (inc + n) inc
  enumFromTo n m = if n <= m 
                   then go (natRange (S (cast {to = Nat} (m - n))))
                   else []
    where go : List Nat -> List Int
          go [] = []
          go (x :: xs) = n + cast x :: go xs
  enumFromThenTo _ 0   _ = []
  enumFromThenTo n inc m = go (natRange (S (cast {to=Nat} (abs (m - n)) `div` cast {to=Nat} (abs inc))))
    where go : List Nat -> List Int
          go [] = []
          go (x :: xs) = n + (cast x * inc) :: go xs

syntax "[" [start] ".." [end] "]"
     = enumFromTo start end
syntax "[" [start] "," [next] ".." [end] "]"
     = enumFromThenTo start (next - start) end

syntax "[" [start] "..]"
     = enumFrom start
syntax "[" [start] "," [next] "..]"
     = enumFromThen start (next - start)

---- More utilities

curry : ((a, b) -> c) -> a -> b -> c
curry f a b = f (a, b)

uncurry : (a -> b -> c) -> (a, b) -> c
uncurry f (a, b) = f a b

uniformB8x16 : Bits8 -> Bits8x16
uniformB8x16 x = prim__mkB8x16 x x x x x x x x x x x x x x x x

uniformB16x8 : Bits16 -> Bits16x8
uniformB16x8 x = prim__mkB16x8 x x x x x x x x

uniformB32x4 : Bits32 -> Bits32x4
uniformB32x4 x = prim__mkB32x4 x x x x

uniformB64x2 : Bits64 -> Bits64x2
uniformB64x2 x = prim__mkB64x2 x x

---- some basic io

partial
putStr : String -> IO ()
putStr x = mkForeign (FFun "putStr" [FString] FUnit) x

partial
putStrLn : String -> IO ()
putStrLn x = putStr (x ++ "\n")

partial
print : Show a => a -> IO ()
print x = putStrLn (show x)

partial
getLine : IO String
getLine = prim_fread prim__stdin

partial
putChar : Char -> IO ()
putChar c = mkForeign (FFun "putchar" [FInt] FUnit) (cast c)

partial
getChar : IO Char
getChar = map cast $ mkForeign (FFun "getchar" [] FInt)

---- some basic file handling

abstract
data File = FHandle Ptr

partial stdin : File
stdin = FHandle prim__stdin

do_fopen : String -> String -> IO Ptr
do_fopen f m
   = mkForeign (FFun "fileOpen" [FString, FString] FPtr) f m

fopen : String -> String -> IO File
fopen f m = do h <- do_fopen f m
               return (FHandle h)

data Mode = Read | Write | ReadWrite

partial
openFile : String -> Mode -> IO File
openFile f m = fopen f (modeStr m) where
  modeStr Read  = "r"
  modeStr Write = "w"
  modeStr ReadWrite = "r+"

partial
do_fclose : Ptr -> IO ()
do_fclose h = mkForeign (FFun "fileClose" [FPtr] FUnit) h

partial
closeFile : File -> IO ()
closeFile (FHandle h) = do_fclose h

partial
do_fread : Ptr -> IO String
do_fread h = prim_fread h

-- mkForeign (FFun "idris_readStr" [FPtr, FPtr] (FAny String))
--                        prim__vm h

partial
fread : File -> IO String
fread (FHandle h) = do_fread h

partial
do_fwrite : Ptr -> String -> IO ()
do_fwrite h s
   = mkForeign (FFun "fputStr" [FPtr, FString] FUnit) h s

partial
fwrite : File -> String -> IO ()
fwrite (FHandle h) s = do_fwrite h s

partial
do_feof : Ptr -> IO Int
do_feof h = mkForeign (FFun "fileEOF" [FPtr] FInt) h

feof : File -> IO Bool
feof (FHandle h) = do eof <- do_feof h
                      return (not (eof == 0))

partial
do_ferror : Ptr -> IO Int
do_ferror h = mkForeign (FFun "fileError" [FPtr] FInt) h

ferror : File -> IO Bool
ferror (FHandle h) = do err <- do_ferror h
                        return (not (err == 0))

partial
nullPtr : Ptr -> IO Bool
nullPtr p = do ok <- mkForeign (FFun "isNull" [FPtr] FInt) p
               return (ok /= 0);

partial
nullStr : String -> IO Bool
nullStr p = do ok <- mkForeign (FFun "isNull" [FString] FInt) p
               return (ok /= 0);

partial
validFile : File -> IO Bool
validFile (FHandle h) = do x <- nullPtr h
                           return (not x)

partial -- obviously
while : |(test : IO Bool) -> |(body : IO ()) -> IO ()
while t b = do v <- t
               if v then do b
                            while t b
                    else return ()

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

