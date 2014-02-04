module Effect.File

import Effects
import Control.IOExcept

data OpenFile : Mode -> Type where
     FH : File -> OpenFile m

openOK : Mode -> Bool -> Type
openOK m True = OpenFile m
openOK m False = ()

data FileIO : Effect where
     Open  : String -> (m : Mode) -> 
             {() ==> {res} if res then OpenFile m else ()} FileIO Bool
     Close : {OpenFile m ==> ()}               FileIO () 

     ReadLine  :           {OpenFile Read}  FileIO String 
     WriteLine : String -> {OpenFile Write} FileIO ()
     EOF       :           {OpenFile Read}  FileIO Bool

instance Handler FileIO IO where
    handle () (Open fname m) k = do h <- openFile fname m
                                    valid <- validFile h
                                    if valid then k True (FH h) 
                                             else k False ()
    handle (FH h) Close      k = do closeFile h
                                    k () ()
    handle (FH h) ReadLine        k = do str <- fread h
                                         k str (FH h)
    handle (FH h) (WriteLine str) k = do fwrite h str
                                         k () (FH h)
    handle (FH h) EOF             k = do e <- feof h
                                         k e (FH h)

FILE_IO : Type -> EFFECT
FILE_IO t = MkEff t FileIO

open : Handler FileIO e =>
       String -> (m : Mode) -> 
       { [FILE_IO ()] ==> [FILE_IO (if result then OpenFile m else ())] } Eff e Bool
open f m = Open f m

close : Handler FileIO e =>
        { [FILE_IO (OpenFile m)] ==> [FILE_IO ()] } Eff e ()
close = Close

readLine : Handler FileIO e => 
           { [FILE_IO (OpenFile Read)] } Eff e String 
readLine = ReadLine

writeLine : Handler FileIO e => 
            String -> { [FILE_IO (OpenFile Write)] } Eff e ()
writeLine str = WriteLine str

eof : Handler FileIO e => 
      { [FILE_IO (OpenFile Read)] } Eff e Bool 
eof = EOF




