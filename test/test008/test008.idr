module main;

testlist : List (String, Int);
testlist = [("foo", 1), ("bar", 2)];

getVal : String -> a -> List (String, a) -> a;
getVal x b xs = case lookup x xs of {
                    Just v  => case lookup x xs of {
                                    Just v' => v
                               }
                  | Nothing => b
                };

foo : (Int, String);
foo = (4, "foo");


ioVals : IO (String, String);
ioVals = do { return ("First", "second"); }; 

main : IO ();
main = do { (a, b) <- ioVals;
            putStr (show a ++ " and " ++ show b ++ "? ");
            let x = "bar";
            putStrLn (show (getVal x 7 testlist));
            let ((y, z) :: _) = testlist;
            print z;
            case lookup x testlist of {
                   Just v => putStrLn (show v)
                 | Nothing => putStrLn "Not there!"
            };
          };

