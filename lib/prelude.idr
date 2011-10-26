import builtins;
import nat;
import list;
import maybe;
import vect;
import io;

---- some basic io

putStr : String -> IO ();
putStr x = mkForeign (FFun "putStr" (Cons FString Nil) FUnit) x;

putStrLn : String -> IO ();
putStrLn x = putStr (x ++ "\n");

readLine : IO String;
readLine = mkForeign (FFun "readStr" Nil FString);

