module Prelude.File

import Builtins
import Prelude.List
import Prelude.Maybe
import Prelude.Monad
import Prelude.Chars
import Prelude.Strings
import Prelude.Cast
import Prelude.Bool
import Prelude.Basics
import Prelude.Classes
import Prelude.Monad
import IO

%access public

||| A file handle
abstract
data File = FHandle Ptr

||| Standard input
stdin : File
stdin = FHandle prim__stdin

||| Standard output
stdout : File
stdout = FHandle prim__stdout

||| Standard output
stderr : File
stderr = FHandle prim__stderr

||| Call the RTS's file opening function
do_fopen : String -> String -> IO Ptr
do_fopen f m
   = foreign FFI_C "fileOpen" (String -> String -> IO Ptr) f m

||| Open a file
||| @ f the filename
||| @ m the mode as a String (`"r"`, `"w"`, or `"r+"`)
fopen : (f : String) -> (m : String) -> IO File
fopen f m = do h <- do_fopen f m
               return (FHandle h)

||| Check whether a file handle is actually a null pointer
partial
validFile : File -> IO Bool
validFile (FHandle h) = do x <- nullPtr h
                           return (not x)

||| Modes for opening files
data Mode = Read | Write | ReadWrite

||| Open a file
||| @ f the filename
||| @ m the mode
partial
openFile : (f : String) -> (m : Mode) -> IO File
openFile f m = fopen f (modeStr m) where
  modeStr Read  = "r"
  modeStr Write = "w"
  modeStr ReadWrite = "r+"

partial
do_fclose : Ptr -> IO ()
do_fclose h = foreign FFI_C "fileClose" (Ptr -> IO ()) h

partial
closeFile : File -> IO ()
closeFile (FHandle h) = do_fclose h

partial
do_fread : Ptr -> IO' l String
do_fread h = prim_fread h

fgetc : File -> IO Char
fgetc (FHandle h) = return (cast !(foreign FFI_C "fgetc" (Ptr -> IO Int) h))

fgetc' : File -> IO (Maybe Char)
fgetc' (FHandle h)
   = do x <- foreign FFI_C "fgetc" (Ptr -> IO Int) h
        if (x < 0) then return Nothing
                   else return (Just (cast x))

fflush : File -> IO ()
fflush (FHandle h) = foreign FFI_C "fflush" (Ptr -> IO ()) h

do_popen : String -> String -> IO Ptr
do_popen f m = foreign FFI_C "do_popen" (String -> String -> IO Ptr) f m

popen : String -> Mode -> IO File
popen f m = do ptr <- do_popen f (modeStr m)
               return (FHandle ptr)
  where
    modeStr Read  = "r"
    modeStr Write = "w"
    modeStr ReadWrite = "r+"

pclose : File -> IO ()
pclose (FHandle h) = foreign FFI_C "pclose" (Ptr -> IO ()) h

-- mkForeign (FFun "idris_readStr" [FPtr, FPtr] (FAny String))
--                        prim__vm h

partial
fread : File -> IO' l String
fread (FHandle h) = do_fread h

partial
do_fwrite : Ptr -> String -> IO ()
do_fwrite h s = do prim_fwrite h s
                   return ()

partial
fwrite : File -> String -> IO ()
fwrite (FHandle h) s = do_fwrite h s

partial
do_feof : Ptr -> IO Int
do_feof h = foreign FFI_C "fileEOF" (Ptr -> IO Int) h

||| Check if a file handle has reached the end
feof : File -> IO Bool
feof (FHandle h) = do eof <- do_feof h
                      return (not (eof == 0))

partial
do_ferror : Ptr -> IO Int
do_ferror h = foreign FFI_C "fileError" (Ptr -> IO Int) h

ferror : File -> IO Bool
ferror (FHandle h) = do err <- do_ferror h
                        return (not (err == 0))

fpoll : File -> IO Bool
fpoll (FHandle h) = do p <- foreign FFI_C "fpoll" (Ptr -> IO Int) h
                       return (p > 0)

||| Read the contents of a file into a string
partial -- no error checking!
readFile : String -> IO String
readFile fn = do h <- openFile fn Read
                 c <- readFile' h ""
                 closeFile h
                 return c
  where
    partial
    readFile' : File -> String -> IO String
    readFile' h contents =
       do x <- feof h
          if not x then do l <- fread h
                           readFile' h (contents ++ l)
                   else return contents


