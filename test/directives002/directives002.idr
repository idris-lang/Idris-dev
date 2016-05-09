module directives002

%access export
%default covering

loop : ()
loop = loop
  
namespace Main
  total
  main : IO ()
  main = do
    pure loop
    putStrLn $ "Hello World"
