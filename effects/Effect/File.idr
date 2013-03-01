module Effect.File

import Effects
import Control.IOExcept

data OpenFile : Mode -> Type where
     FH : File -> OpenFile m

data FileIO : Effect where
     Open  : String -> (m : Mode) -> FileIO () (OpenFile m) ()
     Close :                         FileIO (OpenFile m) () ()

     ReadLine  :           FileIO (OpenFile Read)  (OpenFile Read) String
     WriteLine : String -> FileIO (OpenFile Write) (OpenFile Write) ()
     EOF       :           FileIO (OpenFile Read)  (OpenFile Read) Bool

instance Handler FileIO IO where
    handle () (Open fname m) k = do h <- openFile fname m
                                    k (FH h) ()
    handle (FH h) Close      k = do closeFile h
                                    k () ()
    handle (FH h) ReadLine        k = do str <- fread h
                                         k (FH h) str
    handle (FH h) (WriteLine str) k = do fwrite h str
                                         k (FH h) ()
    handle (FH h) EOF             k = do e <- feof h
                                         k (FH h) e

instance Handler FileIO (IOExcept String) where
    handle () (Open fname m) k 
       = do h <- ioe_lift (openFile fname m)
            valid <- ioe_lift (validFile h)
            if valid then k (FH h) ()
                     else ioe_fail "File open failed"
    handle (FH h) Close           k = do ioe_lift (closeFile h); k () ()
    handle (FH h) ReadLine        k = do str <- ioe_lift (fread h)
                                         k (FH h) str
    handle (FH h) (WriteLine str) k = do ioe_lift (fwrite h str)
                                         k (FH h) ()
    handle (FH h) EOF             k = do e <- ioe_lift (feof h)
                                         k (FH h) e

FILE_IO : Type -> EFF
FILE_IO t = MkEff t FileIO 

open : Handler FileIO e =>
       String -> (m : Mode) -> EffM e [FILE_IO ()] [FILE_IO (OpenFile m)] ()
open f m = Open f m

close : Handler FileIO e =>
        EffM e [FILE_IO (OpenFile m)] [FILE_IO ()] ()
close = Close

readLine : Handler FileIO e => Eff e [FILE_IO (OpenFile Read)] String
readLine = ReadLine

writeLine : Handler FileIO e => String -> Eff e [FILE_IO (OpenFile Write)] ()
writeLine str = WriteLine str

eof : Handler FileIO e => Eff e [FILE_IO (OpenFile Read)] Bool
eof = EOF




