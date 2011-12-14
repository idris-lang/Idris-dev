> module lit;

Test some string primitives while we're at it

> st : String;
> st = "abcdefg";
  
Literate main program

> main : IO ();
> main = do { putStrLn (show (strHead st));
>             putStrLn (show (strIndex st 3));
>             putStrLn (strCons 'z' st);
>             putStrLn (rev st); };

