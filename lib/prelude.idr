module prelude;

import builtins;
import io;

import prelude.nat;
import prelude.list;
import prelude.maybe;
import prelude.either;
import prelude.vect;

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

---- some mathematical operations

%include "math.h"
%lib "m"

exp : Float -> Float;
exp x = prim__floatExp x;

log : Float -> Float;
log x = prim__floatLog x;

---- some basic io

putStr : String -> IO ();
putStr x = mkForeign (FFun "putStr" (FString :: Nil) FUnit) x;

putStrLn : String -> IO ();
putStrLn x = putStr (x ++ "\n");

print : Show a => a -> IO ();
print x = putStrLn (show x);

readLine : IO String;
readLine = mkForeign (FFun "readStr" Nil FString);

---- some basic file handling

data File = FHandle Ptr;

do_fopen : String -> String -> IO Ptr;
do_fopen f m = mkForeign (FFun "fileOpen" [FString, FString] FPtr) f m;

fopen : String -> String -> IO File;
fopen f m = do { h <- do_fopen f m;
                 return (FHandle h); };

do_fclose : Ptr -> IO ();
do_fclose h = mkForeign (FFun "fileClose" [FPtr] FUnit) h;

fclose : File -> IO ();
fclose (FHandle h) = do_fclose h;

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




