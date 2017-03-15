module Prelude.File

import Builtins
import Prelude.List
import Prelude.Maybe
import Prelude.Monad
import Prelude.Chars
import Prelude.Strings
import Prelude.Nat
import Prelude.Cast
import Prelude.Bool
import Prelude.Basics
import Prelude.Interfaces
import Prelude.Either
import Prelude.Show
import IO

%access public export

||| A file handle
data File : Type where
  FHandle : (p : Ptr) -> File

-- Usage hints for erasure analysis
%used FHandle p

||| An error from a file operation
-- This is built in idris_mkFileError() in rts/idris_stdfgn.c. Make sure
-- the values correspond!
               
data FileError = GenericFileError Int -- errno
               | FileReadError
               | FileWriteError
               | FileNotFound
               | PermissionDenied

private
strError : Int -> String
strError err = unsafePerformIO -- yeah, yeah...
                  (foreign FFI_C "idris_showerror" (Int -> IO String) err)

getFileError : IO FileError
getFileError = do vm <- getMyVM
                  MkRaw err <- foreign FFI_C "idris_mkFileError"
                                    (Ptr -> IO (Raw FileError)) vm
                  pure err

Show FileError where
  show FileReadError = "File Read Error"
  show FileWriteError = "File Write Error"
  show FileNotFound = "File Not Found"
  show PermissionDenied = "Permission Denied"
  show (GenericFileError errno) = strError errno

||| Standard input
export
stdin : File
stdin = FHandle prim__stdin

||| Standard output
export
stdout : File
stdout = FHandle prim__stdout

||| Standard output
export
stderr : File
stderr = FHandle prim__stderr

private
do_ferror : Ptr -> IO Int
do_ferror h = foreign FFI_C "fileError" (Ptr -> IO Int) h

export
ferror : File -> IO Bool
ferror (FHandle h) = do err <- do_ferror h
                        pure (not (err == 0))

||| Call the RTS's file opening function
private
do_fopen : String -> String -> IO Ptr
do_fopen f m
   = foreign FFI_C "fileOpen" (String -> String -> IO Ptr) f m

||| Open a file
||| @ f the filename
||| @ m the mode as a String (`"r"`, `"w"`, or `"r+"`)
export
fopen : (f : String) -> (m : String) -> IO (Either FileError File)
fopen f m = do h <- do_fopen f m
               if !(nullPtr h)
                  then do err <- getFileError
                          pure (Left err)
                  else pure (Right (FHandle h))

||| Check whether a file handle is actually a null pointer
export
validFile : File -> IO Bool
validFile (FHandle h) = do x <- nullPtr h
                           pure (not x)

||| Modes for opening files
data Mode = Read | WriteTruncate | Append | ReadWrite | ReadWriteTruncate | ReadAppend

Write : Mode
Write = WriteTruncate
%deprecate Write "Please use WriteTruncate instead."

modeStr : Mode -> String
modeStr Read              = "r"
modeStr WriteTruncate     = "w"
modeStr Append            = "a"
modeStr ReadWrite         = "r+"
modeStr ReadWriteTruncate = "w+"
modeStr ReadAppend        = "a+"

||| Open a file
||| @ f the filename
||| @ m the mode; either Read, WriteTruncate, Append, ReadWrite, ReadWriteTruncate, or ReadAppend
export
openFile : (f : String) -> (m : Mode) -> IO (Either FileError File)
openFile f m = fopen f (modeStr m)

||| Open a file using C11 extended modes.
||| @ f the filename
||| @ m the mode; either Read, WriteTruncate, Append, ReadWrite, ReadWriteTruncate, or ReadAppend
export
openFileX : (f : String) -> (m : Mode) -> IO (Either FileError File)
openFileX f m = fopen f $ modeStr m ++ "x"

private
do_fclose : Ptr -> IO ()
do_fclose h = foreign FFI_C "fileClose" (Ptr -> IO ()) h

export
closeFile : File -> IO ()
closeFile (FHandle h) = do_fclose h

private
do_getFileSize : Ptr -> IO Int
do_getFileSize h = foreign FFI_C "fileSize" (Ptr -> IO Int) h

||| Return the size of a File
||| Returns an error if the File is not an ordinary file (e.g. a directory)
||| Also note that this currently returns an Int, which may overflow if the 
||| file is very big
export
fileSize : File -> IO (Either FileError Int)
fileSize (FHandle h) = do s <- do_getFileSize h
                          if (s < 0) 
                             then do err <- getFileError
                                     pure (Left err)
                             else pure (Right s)

private
do_fread : Ptr -> IO' l String
do_fread h = prim_fread h

private
do_freadChars : Ptr -> Int -> IO' l String
do_freadChars h len = prim_freadChars len h

export
fgetc : File -> IO (Either FileError Char)
fgetc (FHandle h) = do let c = cast !(foreign FFI_C "fgetc" (Ptr -> IO Int) h)
                       if !(ferror (FHandle h))
                          then pure (Left FileReadError)
                          else pure (Right c)

export
fflush : File -> IO ()
fflush (FHandle h) = foreign FFI_C "fflush" (Ptr -> IO ()) h

private
do_popen : String -> String -> IO Ptr
do_popen f m = foreign FFI_C "do_popen" (String -> String -> IO Ptr) f m

export
popen : String -> Mode -> IO (Either FileError File)
popen f m = do ptr <- do_popen f (modeStr m)
               if !(nullPtr ptr)
                  then do err <- getFileError
                          pure (Left err)
                  else pure (Right (FHandle ptr))

export
pclose : File -> IO ()
pclose (FHandle h) = foreign FFI_C "pclose" (Ptr -> IO ()) h

-- mkForeign (FFun "idris_readStr" [FPtr, FPtr] (FAny String))
--                        prim__vm h

export
fread : File -> IO (Either FileError String)
fread (FHandle h) = do str <- do_fread h
                       if !(ferror (FHandle h))
                          then pure (Left FileReadError)
                          else pure (Right str)

||| Read a line from a file
||| @h a file handle which must be open for reading
export
fGetLine : (h : File) -> IO (Either FileError String)
fGetLine = fread

||| Read up to a number of characters from a file
||| @h a file handle which must be open for reading
export
fGetChars : (h : File) -> (len : Int) -> IO (Either FileError String)
fGetChars (FHandle h) len = do str <- do_freadChars h len
                               if !(ferror (FHandle h))
                                  then pure (Left FileReadError)
                                  else pure (Right str)

%deprecate fread "Use fGetLine instead"

private
do_fwrite : Ptr -> String -> IO (Either FileError ())
do_fwrite h s = do res <- prim_fwrite h s
                   if (res /= 0)
                      then do errno <- getErrno
                              if errno == 0
                                 then pure (Left FileWriteError)
                                 else do err <- getFileError
                                         pure (Left err)
                      else pure (Right ())

export
fwrite : File -> String -> IO (Either FileError ())
fwrite (FHandle h) s = do_fwrite h s

||| Write a line to a file
||| @h a file handle which must be open for writing
||| @str the line to write to the file
export
fPutStr : (h : File) -> (str : String) -> IO (Either FileError ())
fPutStr (FHandle h) s = do_fwrite h s

export
fPutStrLn : File -> String -> IO (Either FileError ())
fPutStrLn (FHandle h) s = do_fwrite h (s ++ "\n")

%deprecate fwrite "Use fPutStr instead"

private
do_feof : Ptr -> IO Int
do_feof h = foreign FFI_C "fileEOF" (Ptr -> IO Int) h

||| Check if a file handle has reached the end
export
fEOF : File -> IO Bool
fEOF (FHandle h) = do eof <- do_feof h
                      pure (not (eof == 0))

||| Check if a file handle has reached the end
export
feof : File -> IO Bool
feof = fEOF

%deprecate feof "Use fEOF instead"

export
fpoll : File -> IO Bool
fpoll (FHandle h) = do p <- foreign FFI_C "fpoll" (Ptr -> IO Int) h
                       pure (p > 0)

||| Read the contents of a text file into a string
||| This checks the size of the file before beginning to read, and only
||| reads that many bytes, to ensure that it remains a total function if
||| the file is appended to while being read.
||| This only works reliably with text files, since it relies on null-terminated
||| strings internally.
||| Returns an error if filepath is not a normal file.
export
readFile : (filepath : String) -> IO (Either FileError String)
readFile fn = do Right h <- openFile fn Read
                    | Left err => pure (Left err)
                 Right max <- fileSize h
                    | Left err => pure (Left err)
                 sb <- newStringBuffer (max + 1)
                 c <- readFile' h max sb
                 closeFile h
                 pure c
  where
    readFile' : File -> Int -> StringBuffer -> IO (Either FileError String)
    readFile' h max contents =
       do x <- fEOF h
          if not x && max > 0
                   then do Right l <- fGetChars h 1024000
                               | Left err => pure (Left err)
                           addToStringBuffer contents l
                           assert_total $
                             readFile' h (max - 1024000) contents
                   else do str <- getStringFromBuffer contents
                           pure (Right str)

||| Write a string to a file
export
writeFile : (filepath : String) -> (contents : String) ->
            IO (Either FileError ())
writeFile fn contents = do
     Right h  <- openFile fn WriteTruncate | Left err => pure (Left err)
     Right () <- fPutStr h contents        | Left err => pure (Left err)
     closeFile h
     pure (Right ())
