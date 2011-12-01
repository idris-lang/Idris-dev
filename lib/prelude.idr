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
print = putStrLn . show;

readLine : IO String;
readLine = mkForeign (FFun "readStr" Nil FString);

