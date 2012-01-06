module prelude;

import builtins;
import io;

import prelude.nat;
import prelude.list;
import prelude.maybe;
import prelude.either;
import prelude.vect;
import prelude.strings;
import prelude.char;

-- Show and instances

class Show a where {
    show : a -> String;
}

instance Show Nat where {
    show O = "O";
    show (S k) = "s" ++ show k;
}

instance Show Int where {
    show = prim__intToStr;
}

instance Show Integer where {
    show = prim__bigIntToStr;
}

instance Show Float where {
    show = prim__floatToStr;
}

instance Show Char where {
    show x = strCons x ""; 
}

instance Show String where {
    show = id;
}

instance Show Bool where {
    show True = "True";
    show False = "False";
}

instance (Show a, Show b) => Show (a, b) where {
    show (x, y) = "(" ++ show x ++ ", " ++ show y ++ ")";
}

instance Show a => Show (List a) where {
    show xs = "[" ++ show' xs ++ "]" where {
        show' : Show a => List a -> String;
        show' []        = "";
        show' [x]       = show x;
        show' (x :: xs) = show x ++ ", " ++ show' xs;
    }
}

instance Show a => Show (Vect a n) where {
    show xs = "[" ++ show' xs ++ "]" where {
        show' : Show a => Vect a n -> String;
        show' []        = "";
        show' [x]       = show x;
        show' (x :: xs) = show x ++ ", " ++ show' xs;
    }
}

instance Show a => Show (Maybe a) where {
    show Nothing = "Nothing";
    show (Just x) = "Just " ++ show x;
}

---- Monad and instances

infixl 5 >>= ;

class Monad (m : Set -> Set) where {
    return : a -> m a;
    (>>=)  : m a -> (a -> m b) -> m b;
}

class Monad m => MonadPlus (m : Set -> Set) where {
    mplus : m a -> m a -> m a;
    mzero : m a;
}

class Monad m => MonadFail (m : Set -> Set) where {
    fail : String -> m ();
}

instance Monad IO where {
    return t = io_return t;
    b >>= k = io_bind b k;
}

instance Monad Maybe where {
    return = Just;

    Nothing  >>= k = Nothing;
    (Just x) >>= k = k x;
}

instance MonadPlus Maybe where {
    mzero = Nothing;

    mplus (Just x) _       = Just x;
    mplus Nothing (Just y) = Just y;
    mplus Nothing Nothing  = Nothing;
}

instance Monad List where {
    return x = [x];
    m >>= f = concatMap f m;
}

instance MonadPlus List where {
    mzero = [];
    mplus = app;
}

guard : MonadPlus m => Bool -> m ();
guard True  = return ();
guard False = mzero;

---- Functors

class Functor (f : Set -> Set) where {
    fmap : (a -> b) -> f a -> f b;
}

instance Functor Maybe where {
    fmap f (Just x) = Just (f x);
    fmap f Nothing  = Nothing;
}

instance Functor List where {
    fmap = map;
}

---- Applicative functors/Idioms

infixl 2 <$>;

class Functor f => Applicative (f : Set -> Set) where {
    pure  : a -> f a;
    (<$>) : f (a -> b) -> f a -> f b; 
}

---- some mathematical operations

%include "math.h"
%lib "m"

exp : Float -> Float;
exp x = prim__floatExp x;

log : Float -> Float;
log x = prim__floatLog x;

pi : Float;
pi = 3.141592653589793;

sin : Float -> Float;
sin x = prim__floatSin x;

cos : Float -> Float;
cos x = prim__floatCos x;

tan : Float -> Float;
tan x = prim__floatTan x;

asin : Float -> Float;
asin x = prim__floatASin x;

acos : Float -> Float;
acos x = prim__floatACos x;

atan : Float -> Float;
atan x = prim__floatATan x;

sqrt : Float -> Float;
sqrt x = prim__floatSqrt x;

floor : Float -> Float;
floor x = prim__floatFloor x;

ceiling : Float -> Float;
ceiling x = prim__floatCeil x;


-- Ranges

count : Num a => a -> a -> a -> List a;
count a inc b = if (a <= b) then (a :: count (a + inc) inc b)
                            else [];
  
syntax "[" [start] ".." [end] "]" 
     = count start 1 end;
syntax "[" [start] "," [next] ".." [end] "]" 
     = count start (next - start) end;

---- some basic io

putStr : String -> IO ();
putStr x = mkForeign (FFun "putStr" [FString] FUnit) x;

putStrLn : String -> IO ();
putStrLn x = putStr (x ++ "\n");

print : Show a => a -> IO ();
print x = putStrLn (show x);

getLine : IO String;
getLine = mkForeign (FFun "readStr" Nil FString);

putChar : Char -> IO ();
putChar c = mkForeign (FFun "putchar" [FChar] FUnit) c;

getChar : IO Char;
getChar = mkForeign (FFun "getchar" [] FChar);

---- some basic file handling

abstract data File = FHandle Ptr;

do_fopen : String -> String -> IO Ptr;
do_fopen f m = mkForeign (FFun "fileOpen" [FString, FString] FPtr) f m;

fopen : String -> String -> IO File;
fopen f m = do { h <- do_fopen f m;
                 return (FHandle h); };

data Mode = Read | Write | ReadWrite;

openFile : String -> Mode -> IO File;
openFile f m = fopen f (modeStr m) where {
  modeStr : Mode -> String;
  modeStr Read  = "r";
  modeStr Write = "w";
  modeStr ReadWrite = "r+";
}

do_fclose : Ptr -> IO ();
do_fclose h = mkForeign (FFun "fileClose" [FPtr] FUnit) h;

closeFile : File -> IO ();
closeFile (FHandle h) = do_fclose h;

do_fread : Ptr -> IO String;
do_fread h = mkForeign (FFun "freadStr" [FPtr] FString) h;

fread : File -> IO String;
fread (FHandle h) = do_fread h;

do_fwrite : Ptr -> String -> IO ();
do_fwrite h s = mkForeign (FFun "fputStr" [FPtr, FString] FUnit) h s;

fwrite : File -> String -> IO ();
fwrite (FHandle h) s = do_fwrite h s;

do_feof : Ptr -> IO Int;
do_feof h = mkForeign (FFun "feof" [FPtr] FInt) h;

feof : File -> IO Bool;
feof (FHandle h) = do { eof <- do_feof h;
                        return (not (eof == 0)); };

while : |(test : IO Bool) -> |(body : IO ()) -> IO ();
while t b = do { v <- t;
                 if v then (do { b; while t b; }) else return (); };

readFile : String -> IO String;
readFile fn = do { h <- openFile fn Read;
                   c <- readFile' h "";
                   closeFile h;
                   return c;
                 }
  where {
    readFile' : File -> String -> IO String;
    readFile' h contents = 
       do { x <- feof h;
            if (not x) then (do { l <- fread h;
                                  readFile' h (contents ++ l);
                                })
                       else (return contents); };
  }

