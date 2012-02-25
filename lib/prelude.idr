module prelude

import builtins
import io

import prelude.cast
import prelude.nat
import prelude.fin
import prelude.list
import prelude.maybe
import prelude.monad
import prelude.applicative
import prelude.either
import prelude.vect
import prelude.strings
import prelude.char

%access public

-- Show and instances

class Show a where 
    show : a -> String

instance Show Nat where 
    show O = "O"
    show (S k) = "s" ++ show k

instance Show Int where 
    show = prim__intToStr

instance Show Integer where 
    show = prim__bigIntToStr

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
        show' : String -> List a -> String
        show' acc []        = acc
        show' acc [x]       = acc ++ show x
        show' acc (x :: xs) = show' (acc ++ show x ++ ", ") xs

instance Show a => Show (Vect a n) where 
    show xs = "[" ++ show' xs ++ "]" where 
        show' : Vect a m -> String
        show' []        = ""
        show' [x]       = show x
        show' (x :: xs) = show x ++ ", " ++ show' xs

instance Show a => Show (Maybe a) where 
    show Nothing = "Nothing"
    show (Just x) = "Just " ++ show x

---- Monad instances

instance Monad IO where 
    return t = io_return t
    b >>= k = io_bind b k

instance Monad Maybe where 
    return t = Just t

    Nothing  >>= k = Nothing
    (Just x) >>= k = k x

instance MonadPlus Maybe where 
    mzero = Nothing

    mplus (Just x) _       = Just x
    mplus Nothing (Just y) = Just y
    mplus Nothing Nothing  = Nothing

instance Monad List where 
    return x = [x]
    m >>= f = concatMap f m

instance MonadPlus List where 
    mzero = []
    mplus = (++)

---- Functor instances

instance Functor Maybe where 
    fmap f (Just x) = Just (f x)
    fmap f Nothing  = Nothing

instance Functor List where 
    fmap = map

---- Applicative instances

instance Applicative Maybe where
    pure = Just

    (Just f) <$> (Just a) = Just (f a)
    _        <$> _        = Nothing


---- some mathematical operations

%include "math.h"
%lib "m"

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

sqrt : Float -> Float
sqrt x = prim__floatSqrt x

floor : Float -> Float
floor x = prim__floatFloor x

ceiling : Float -> Float
ceiling x = prim__floatCeil x

---- Ranges

count : (Ord a, Num a) => a -> a -> a -> List a
count a inc b = if a <= b then a :: count (a + inc) inc b
                          else []
  
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

---- some basic io

putStr : String -> IO ()
putStr x = mkForeign (FFun "putStr" [FString] FUnit) x

putStrLn : String -> IO ()
putStrLn x = putStr (x ++ "\n")

print : Show a => a -> IO ()
print x = putStrLn (show x)

getLine : IO String
getLine = mkForeign (FFun "readStr" Nil FString)

putChar : Char -> IO ()
putChar c = mkForeign (FFun "putchar" [FChar] FUnit) c

getChar : IO Char
getChar = mkForeign (FFun "getchar" [] FChar)

---- some basic file handling

abstract 
data File = FHandle Ptr

do_fopen : String -> String -> IO Ptr
do_fopen f m = mkForeign (FFun "fileOpen" [FString, FString] FPtr) f m

fopen : String -> String -> IO File
fopen f m = do h <- do_fopen f m
               return (FHandle h) 

data Mode = Read | Write | ReadWrite

openFile : String -> Mode -> IO File
openFile f m = fopen f (modeStr m) where 
  modeStr : Mode -> String
  modeStr Read  = "r"
  modeStr Write = "w"
  modeStr ReadWrite = "r+"

do_fclose : Ptr -> IO ()
do_fclose h = mkForeign (FFun "fileClose" [FPtr] FUnit) h

closeFile : File -> IO ()
closeFile (FHandle h) = do_fclose h

do_fread : Ptr -> IO String
do_fread h = mkForeign (FFun "freadStr" [FPtr] FString) h

fread : File -> IO String
fread (FHandle h) = do_fread h

do_fwrite : Ptr -> String -> IO ()
do_fwrite h s = mkForeign (FFun "fputStr" [FPtr, FString] FUnit) h s

fwrite : File -> String -> IO ()
fwrite (FHandle h) s = do_fwrite h s

do_feof : Ptr -> IO Int
do_feof h = mkForeign (FFun "feof" [FPtr] FInt) h

feof : File -> IO Bool
feof (FHandle h) = do eof <- do_feof h
                      return (not (eof == 0)) 

nullPtr : Ptr -> IO Bool
nullPtr p = do ok <- mkForeign (FFun "isNull" [FPtr] FInt) p 
               return (ok /= 0);

validFile : File -> IO Bool
validFile (FHandle h) = do x <- nullPtr h
                           return (not x)

while : |(test : IO Bool) -> |(body : IO ()) -> IO ()
while t b = do v <- t
               if v then do b
                            while t b
                    else return ()
               

readFile : String -> IO String
readFile fn = do h <- openFile fn Read
                 c <- readFile' h ""
                 closeFile h
                 return c
  where 
    readFile' : File -> String -> IO String
    readFile' h contents = 
       do x <- feof h
          if not x then do l <- fread h
                           readFile' h (contents ++ l)
                   else return contents

