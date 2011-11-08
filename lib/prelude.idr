import builtins;
import nat;
import list;
import maybe;
import vect;
import io;

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
        show' Nil = "";
        show' (Cons x Nil) = show x;
        show' (Cons x xs) = show x ++ ", " ++ show' xs;
    }
}

instance Show a => Show (Vect a n) where {
    show xs = "[" ++ show' xs ++ "]" where {
        show' : Show a => Vect a n -> String;
        show' VNil = "";
        show' (x :: VNil) = show x;
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


---- some basic io

putStr : String -> IO ();
putStr x = mkForeign (FFun "putStr" (Cons FString Nil) FUnit) x;

putStrLn : String -> IO ();
putStrLn x = putStr (x ++ "\n");

print : Show a => a -> IO ();
print = putStrLn . show;

readLine : IO String;
readLine = mkForeign (FFun "readStr" Nil FString);

