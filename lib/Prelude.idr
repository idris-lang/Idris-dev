module Prelude

import Builtins
import IO

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

%access public
%default total

-- Show and instances

class Show a where 
    show : a -> String

instance Show Nat where 
    show O = "O"
    show (S k) = "s" ++ show k

instance Show Int where 
    show = prim__toStrInt

instance Show Integer where 
    show = prim__toStrBigInt

instance Show Float where 
    show = prim__floatToStr

instance Show Char where 
    show x = strCons x "" 

instance Show String where 
    show = id

instance Show Bool where 
    show True = "True"
    show False = "False"

instance (Show a, Show b) => Show (a, b) where 
    show (x, y) = "(" ++ show x ++ ", " ++ show y ++ ")"

instance Show a => Show (List a) where 
    show xs = "[" ++ show' "" xs ++ "]" where 
        show' acc []        = acc
        show' acc [x]       = acc ++ show x
        show' acc (x :: xs) = show' (acc ++ show x ++ ", ") xs

instance Show a => Show (Vect a n) where 
    show xs = "[" ++ show' xs ++ "]" where 
        show' : Vect a n -> String
        show' []        = ""
        show' [x]       = show x
        show' (x :: xs) = show x ++ ", " ++ show' xs

instance Show a => Show (Maybe a) where 
    show Nothing = "Nothing"
    show (Just x) = "Just " ++ show x

---- Functor instances

instance Functor IO where
    fmap f io = io_bind io (io_return . f)

instance Functor Maybe where 
    fmap f (Just x) = Just (f x)
    fmap f Nothing  = Nothing

instance Functor (Either e) where
    fmap f (Left l) = Left l
    fmap f (Right r) = Right (f r)

instance Functor List where 
    fmap = map

---- Applicative instances

instance Applicative IO where
    pure = io_return
    
    am <$> bm = io_bind am (\f => io_bind bm (io_return . f))

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

---- Alternative instances

instance Alternative Maybe where
    empty = Nothing

    (Just x) <|> _ = Just x
    Nothing  <|> v = v

instance Alternative List where
    empty = []
    
    (<|>) = (++)

---- Monad instances

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

---- some mathematical operations

%include "math.h"
%lib "m"

pow : (Num a) => a -> Nat -> a
pow x O = 1
pow x (S n) = x * (pow x n)

exp : Float -> Float
exp x = prim__floatExp x

log : Float -> Float
log x = prim__floatLog x

pi : Float
pi = 3.141592653589793

sin : Float -> Float
sin x = prim__floatSin x

cos : Float -> Float
cos x = prim__floatCos x

tan : Float -> Float
tan x = prim__floatTan x

asin : Float -> Float
asin x = prim__floatASin x

acos : Float -> Float
acos x = prim__floatACos x

atan : Float -> Float
atan x = prim__floatATan x

atan2 : Float -> Float -> Float
atan2 y x = atan (y/x)

sinh : Float -> Float
sinh x = (exp x - exp (-x)) / 2

cosh : Float -> Float
cosh x = (exp x + exp (-x)) / 2

tanh : Float -> Float
tanh x = sinh x / cosh x

sqrt : Float -> Float
sqrt x = prim__floatSqrt x

floor : Float -> Float
floor x = prim__floatFloor x

ceiling : Float -> Float
ceiling x = prim__floatCeil x

---- Ranges

partial abstract
count : (Ord a, Num a) => a -> a -> a -> List a
count a inc b = if a <= b then a :: count (a + inc) inc b
                          else []
  
partial abstract
countFrom : (Ord a, Num a) => a -> a -> List a
countFrom a inc = a :: lazy (countFrom (a + inc) inc)
  
syntax "[" [start] ".." [end] "]" 
     = count start 1 end 
syntax "[" [start] "," [next] ".." [end] "]" 
     = count start (next - start) end 

syntax "[" [start] "..]" 
     = countFrom start 1
syntax "[" [start] "," [next] "..]" 
     = countFrom start (next - start)

---- More utilities

sum : Num a => List a -> a
sum = foldl (+) 0

prod : Num a => List a -> a
prod = foldl (*) 1

curry : ((a, b) -> c) -> a -> b -> c
curry f a b = f (a, b)

uncurry : (a -> b -> c) -> (a, b) -> c
uncurry f (a, b) = f a b

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
getLine = return (prim__readString prim__stdin)

partial
putChar : Char -> IO ()
putChar c = mkForeign (FFun "putchar" [FInt] FUnit) (cast c)

partial
getChar : IO Char
getChar = fmap cast $ mkForeign (FFun "getchar" [] FInt)

---- some basic file handling

data File = FHandle Ptr

partial stdin : File
stdin = FHandle prim__stdin

do_fopen : String -> String -> IO Ptr
do_fopen f m = mkForeign (FFun "fileOpen" [FString, FString] FPtr) f m

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
do_fread h = return (prim__readString h)

partial
fread : File -> IO String
fread (FHandle h) = do_fread h

partial
do_fwrite : Ptr -> String -> IO ()
do_fwrite h s = mkForeign (FFun "fputStr" [FPtr, FString] FUnit) h s

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
do_fileLength : Ptr -> IO Int
do_fileLength h = mkForeign (FFun "idris_fileLength" [FPtr] FInt) h

fileLength : File -> IO Nat
fileLength (FHandle ptr) = do l <- do_fileLength ptr
                              return (fromInteger l)

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

