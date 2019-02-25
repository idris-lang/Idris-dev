module Main

export
f : JS_IO ()
f = do
    let res = ()
    let res2 = res
    let res3 = res
    putStrLn' "Hello?"

lib : FFI_Export FFI_JS "" []
lib =
    Fun f "f" $
    End
