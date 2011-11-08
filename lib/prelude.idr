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

instance showNat : Show Nat;
instance showNat = instanceShow show where {
    show : Nat -> String;
    show O = "O";
    show (S k) = "s" ++ show k;
}

{-
 
instance Show Nat where {
    show O = "O";
    show (S k) = "s" ++ show k;
}

-}

instance showInt : Show Int;
instance showInt = instanceShow show where {
    show : Int -> String;
    show = prim__intToStr;
}

instance showFloat : Show Float;
instance showFloat = instanceShow show where {
    show : Float -> String;
    show = prim__floatToStr;
}

instance showList : Show a => Show (List a);
instance showList = instanceShow lshow where {
    lshow : Show a => List a -> String;
    lshow xs = "[" ++ show' xs ++ "]" where {
        show' : Show a => List a -> String;
        show' Nil = "";
        show' (Cons x Nil) = show x;
        show' (Cons x xs') = show x ++ ", " ++ show' xs';
    }
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

