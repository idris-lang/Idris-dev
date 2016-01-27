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
import Prelude.Interfaces
import Prelude.Either
import Prelude.Show
import IO

%access public

||| A file handle
abstract
data File : Type where
  FHandle : (p : Ptr) -> File

-- Usage hints for erasure analysis
%used FHandle p

||| An error from a file operation
-- This is built in idris_mkFileError() in rts/idris_stdfgn.c. Make sure
-- the values correspond!
data FileError = FileReadError
               | FileWriteError
               | FileNotFound
               | PermissionDenied
               | GenericFileError Int -- errno

private
strError : Int -> String
strError err = unsafePerformIO -- yeah, yeah...
                  (foreign FFI_C "idris_showerror" (Int -> IO String) err)

getFileError : IO FileError
getFileError = do MkRaw err <- foreign FFI_C "idris_mkFileError"
                                    (Ptr -> IO (Raw FileError)) prim__vm
                  return err

Show FileError where
  show FileNotFound = "File Not Found"
  show PermissionDenied = "Permission Denied"
  show (GenericFileError errno) = strError errno

||| Standard input
stdin : File
stdin = FHandle prim__stdin

||| Standard output
stdout : File
stdout = FHandle prim__stdout

||| Standard output
stderr : File
stderr = FHandle prim__stderr

do_ferror : Ptr -> IO Int
do_ferror h = foreign FFI_C "fileError" (Ptr -> IO Int) h

ferror : File -> IO Bool
ferror (FHandle h) = do err <- do_ferror h
                        return (not (err == 0))

||| Call the RTS's file opening function
do_fopen : String -> String -> IO Ptr
do_fopen f m
   = foreign FFI_C "fileOpen" (String -> String -> IO Ptr) f m

||| Open a file
||| @ f the filename
||| @ m the mode as a String (`"r"`, `"w"`, or `"r+"`)
fopen : (f : String) -> (m : String) -> IO (Either FileError File)
fopen f m = do h <- do_fopen f m
               if !(nullPtr h)
                  then do err <- getFileError
                          return (Left err)
                  else return (Right (FHandle h))

||| Check whether a file handle is actually a null pointer
validFile : File -> IO Bool
validFile (FHandle h) = do x <- nullPtr h
                           return (not x)

||| Modes for opening files
data Mode = Read | Write | ReadWrite

||| Open a file
||| @ f the filename
||| @ m the mode; either Read, Write, or ReadWrite
openFile : (f : String) -> (m : Mode) -> IO (Either FileError File)
openFile f m = fopen f (modeStr m) where
  modeStr Read  = "r"
  modeStr Write = "w"
  modeStr ReadWrite = "r+"

do_fclose : Ptr -> IO ()
do_fclose h = foreign FFI_C "fileClose" (Ptr -> IO ()) h

closeFile : File -> IO ()
closeFile (FHandle h) = do_fclose h

do_fread : Ptr -> IO' l String
do_fread h = prim_fread h

fgetc : File -> IO (Either FileError Char)
fgetc (FHandle h) = do let c = cast !(foreign FFI_C "fgetc" (Ptr -> IO Int) h)
                       if !(ferror (FHandle h))
                          then return (Left FileReadError)
                          else return (Right c)

fflush : File -> IO ()
fflush (FHandle h) = foreign FFI_C "fflush" (Ptr -> IO ()) h

do_popen : String -> String -> IO Ptr
do_popen f m = foreign FFI_C "do_popen" (String -> String -> IO Ptr) f m

popen : String -> Mode -> IO (Either FileError File)
popen f m = do ptr <- do_popen f (modeStr m)
               if !(nullPtr ptr)
                  then do err <- getFileError
                          return (Left err)
                  else return (Right (FHandle ptr))
  where
    modeStr Read  = "r"
    modeStr Write = "w"
    modeStr ReadWrite = "r+"

pclose : File -> IO ()
pclose (FHandle h) = foreign FFI_C "pclose" (Ptr -> IO ()) h

-- mkForeign (FFun "idris_readStr" [FPtr, FPtr] (FAny String))
--                        prim__vm h

fread : File -> IO (Either FileError String)
fread (FHandle h) = do str <- do_fread h
                       if !(ferror (FHandle h))
                          then return (Left FileReadError)
                          else return (Right str)

||| Read a line from a file
||| @h a file handle which must be open for reading
fGetLine : (h : File) -> IO (Either FileError String)
fGetLine = fread

%deprecate fread "Use fGetLine instead"

do_fwrite : Ptr -> String -> IO (Either FileError ())
do_fwrite h s = do res <- prim_fwrite h s
                   if (res /= 0)
                      then do errno <- getErrno
                              if errno == 0
                                 then return (Left FileWriteError)
                                 else do err <- getFileError
                                         return (Left err)
                      else return (Right ())

fwrite : File -> String -> IO (Either FileError ())
fwrite (FHandle h) s = do_fwrite h s

||| Write a line to a file
||| @h a file handle which must be open for writing
||| @str the line to write to the file
fPutStr : (h : File) -> (str : String) -> IO (Either FileError ())
fPutStr (FHandle h) s = do_fwrite h s

fPutStrLn : File -> String -> IO (Either FileError ())
fPutStrLn (FHandle h) s = do_fwrite h (s ++ "\n")

%deprecate fwrite "Use fPutStr instead"

do_feof : Ptr -> IO Int
do_feof h = foreign FFI_C "fileEOF" (Ptr -> IO Int) h

||| Check if a file handle has reached the end
fEOF : File -> IO Bool
fEOF (FHandle h) = do eof <- do_feof h
                      return (not (eof == 0))

||| Check if a file handle has reached the end
feof : File -> IO Bool
feof = fEOF

%deprecate feof "Use fEOF instead"

fpoll : File -> IO Bool
fpoll (FHandle h) = do p <- foreign FFI_C "fpoll" (Ptr -> IO Int) h
                       return (p > 0)

||| Read the contents of a file into a string
partial -- might be reading something infinitely long like /dev/null ...
covering
readFile : String -> IO (Either FileError String)
readFile fn = do Right h <- openFile fn Read
                    | Left err => return (Left err)
                 c <- readFile' h ""
                 closeFile h
                 return c
  where
    partial
    readFile' : File -> String -> IO (Either FileError String)
    readFile' h contents =
       do x <- fEOF h
          if not x then do Right l <- fGetLine h
                               | Left err => return (Left err)
                           readFile' h (contents ++ l)
                   else return (Right contents)

||| Write a string to a file
writeFile : (filepath : String) -> (contents : String) ->
            IO (Either FileError ())
writeFile fn contents = do
     Right h <- openFile fn Write | Left err => return (Left err)
     Right () <- fPutStr h contents | Left err => return (Left err)
     closeFile h
     return (Right ())
