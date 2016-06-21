||| Effectful file operations.
module Effect.File

import Effects
import Control.IOExcept

%access public export

-- -------------------------------------------------------------- [ Predicates ]

||| A record of the file modes that can read from a file.
data ValidModeRead : Mode -> Type where
  VMRRead   : ValidModeRead Read
  VMRReadW  : ValidModeRead ReadWrite
  VMRReadWT : ValidModeRead ReadWriteTruncate
  VMRReadA  : ValidModeRead ReadAppend

||| A record of the file modes that can write from a file.
data ValidModeWrite : Mode -> Type where
  VMWWrite  : ValidModeWrite WriteTruncate
  VMWAppend : ValidModeWrite Append
  VMWReadW  : ValidModeWrite ReadWrite
  VMWReadWT : ValidModeWrite ReadWriteTruncate

-- -------------------------------------------------- [ Custom Error Reporting ]

namespace FileResult

  ||| A type to describe the return type of file operations.
  data ResultDesc = SUCCESS | RESULT

  ||| A custom return type for file operations that is dependent on
  ||| the type of file operation.
  |||
  ||| @desc Parameterises the constructors to describe if the function
  |||       returns a value or not.
  ||| @ty   The return type for a file operation that returns a value.
  |||
  data FileOpReturnTy : (desc : ResultDesc)
                     -> (ty : Type)
                     -> Type where

    ||| The operation completed successfully and doesn't return a
    ||| result.
    Success : FileOpReturnTy SUCCESS ty

    ||| The operation returns a result of type `ty`.
    |||
    ||| @ty The value returned.
    Result : ty -> FileOpReturnTy RESULT ty

    ||| The operation failed and the RTS produced the given error.
    |||
    ||| @err The reported error code.
    FError : (err : FileError) -> FileOpReturnTy desc ty

  ||| Type alias to describe a file operatons that returns a result.
  FileOpResult : Type -> Type
  FileOpResult ty = FileOpReturnTy RESULT ty

  ||| Type alias to describe file oeprations that indicate success.
  FileOpSuccess : Type
  FileOpSuccess = FileOpReturnTy SUCCESS ()

-- ------------------------------------------------------------ [ The Resource ]

||| The file handle associated with the effect.
|||
||| @m The `Mode` that the handle was generated under.
data FileHandle : (m : Mode) -> Type where
    FH : File -> FileHandle m

-- ---------------------------------------------- [ Resource Type Construction ]

||| Calculates the type for the resource being computed over.  `Unit`
||| to describe pre-and-post file handle acquisistion, and `FileHandle
||| m` when a file handle has been aqcuired.
|||
||| @m The mode the file handle was generated under.
||| @ty The functions return type.
calcResourceTy : (m  : Mode)
              -> (ty : FileOpReturnTy fOpTy retTy)
              -> Type
calcResourceTy _ (FError e) = ()
calcResourceTy m _          = FileHandle m

-- ------------------------------------------------------- [ Effect Definition ]

||| An effect to describe operations on a file.
data FileE : Effect where

  -- Open/Close

  Open : (fname : String)
      -> (m : Mode)
      -> sig FileE
             (FileOpSuccess)
             ()
             (\res => calcResourceTy m res)

  OpenX : (fname : String)
       -> (m : Mode)
       -> sig FileE
              (FileOpSuccess)
              ()
              (\res => calcResourceTy m res)

  Close : sig FileE () (FileHandle m) ()

  -- Read

  FGetC : {auto prf : ValidModeRead m}
       -> sig FileE
              (FileOpResult Char)
              (FileHandle m)
              (FileHandle m)

  FGetLine : {auto prf : ValidModeRead m}
          -> sig FileE
                 (FileOpResult String)
                 (FileHandle m)
                 (FileHandle m)

  FReadFile : (fname : String)
           -> sig FileE
                  (FileOpResult String)
                  ()
                  ()
  -- Write
  FPutStr : (str : String)
         -> {auto prf : ValidModeWrite m}
         -> sig FileE
                (FileOpSuccess)
                (FileHandle m)
                (FileHandle m)

  FPutStrLn : (str : String)
           -> {auto prf : ValidModeWrite m}
           -> sig FileE
                  (FileOpSuccess)
                  (FileHandle m)
                  (FileHandle m)

  FWriteFile : (fname    : String)
            -> (contents : String)
            -> sig FileE
                   (FileOpSuccess)
                   ()

  -- Flush
  FFlush : sig FileE
               ()
               (FileHandle m)
               (FileHandle m)

  -- Query
  FEOF : {auto prf : ValidModeRead m}
      -> sig FileE
             Bool
             (FileHandle m)

-- ---------------------------------------------------------------------- [ IO ]

Handler FileE IO where

  -- Open Close
  handle () (Open fname m) k = do
      res <- openFile fname m
      case res of
        Left err => k (FError err) ()
        Right fh => k Success      (FH fh)

  handle () (OpenX fname m) k = do
      res <- openFileX fname m
      case res of
        Left err => k (FError err) ()
        Right fh => k Success      (FH fh)

  handle (FH h) Close k = do
      closeFile h
      k () ()

  -- Read
  handle (FH h) FGetC k = do
      res <- fgetc h
      case res of
        Left err => k (FError err) (FH h)
        Right  c => k (Result c)   (FH h)

  handle (FH h) FGetLine k = do
      res <- fGetLine h
      case res of
        Left err => k (FError err) (FH h)
        Right ln => k (Result ln)  (FH h)

  handle () (FReadFile fname) k = do
      res <- readFile fname
      case res of
        Left err  => k (FError err) ()
        Right str => k (Result str) ()

  -- Write
  handle (FH fh) (FPutStr str) k = do
      res <- fPutStr fh str
      case res of
        Left err => k (FError err) (FH fh)
        Right () => k Success      (FH fh)

  handle (FH fh) (FPutStrLn str) k = do
      res <- fPutStr fh str
      case res of
        Left err => k (FError err) (FH fh)
        Right () => k Success      (FH fh)

  handle () (FWriteFile fname str) k = do
      res <- writeFile fname str
      case res of
        Left err => k (FError err) ()
        Right () => k Success      ()

  -- Flush
  handle (FH fh) FFlush k = do
      fflush fh
      k () (FH fh)

  -- Query
  handle (FH fh) FEOF k = do
      res <- fEOF fh
      k res (FH fh)

-- ---------------------------------------------------------------- [ IOExcept ]

Handler FileE (IOExcept a) where

  -- Open Close
  handle () (Open fname m) k = do
      res <- ioe_lift $ openFile fname m
      case res of
        Left err => k (FError err) ()
        Right fh => k Success      (FH fh)

  handle () (OpenX fname m) k = do
      res <- ioe_lift $ openFileX fname m
      case res of
        Left err => k (FError err) ()
        Right fh => k Success      (FH fh)

  handle (FH h) Close k = do
      ioe_lift $ closeFile h
      k () ()

  -- Read
  handle (FH h) FGetC k = do
      res <- ioe_lift $ fgetc h
      case res of
        Left err => k (FError err) (FH h)
        Right  c => k (Result c)   (FH h)

  handle (FH h) FGetLine k = do
      res <- ioe_lift $ fGetLine h
      case res of
        Left err => k (FError err) (FH h)
        Right ln => k (Result ln)  (FH h)

  handle () (FReadFile fname) k = do
      res <- ioe_lift $ readFile fname
      case res of
        Left err  => k (FError err) ()
        Right str => k (Result str) ()

  -- Write
  handle (FH fh) (FPutStr str) k = do
      res <- ioe_lift $ fPutStr fh str
      case res of
        Left err => k (FError err) (FH fh)
        Right () => k Success      (FH fh)

  handle (FH fh) (FPutStrLn str) k = do
      res <- ioe_lift $ fPutStr fh str
      case res of
        Left err => k (FError err) (FH fh)
        Right () => k Success      (FH fh)

  handle () (FWriteFile fname str) k = do
      res <- ioe_lift $ writeFile fname str
      case res of
        Left err => k (FError err) ()
        Right () => k Success      ()

  -- Flush
  handle (FH fh) FFlush k = do
      ioe_lift $ fflush fh
      k () (FH fh)


  -- Query
  handle (FH fh) FEOF k = do
      res <- ioe_lift $ fEOF fh
      k res (FH fh)

-- ------------------------------------------------------ [ Effect and Helpers ]

||| Effectful operations for interacting with files.
|||
||| The `FILE` effect is parameterised by a file handle once a handle has been acquired, and Unit (`()`) if the file handle is expected to be released once the function has returned.
|||
FILE : (ty : Type) -> EFFECT
FILE t = MkEff t FileE

||| A file has been opened for reading.
R : Type
R = FileHandle Read

||| A file has been opened for writing.
W : Type
W = FileHandle WriteTruncate

||| A file can only be appeneded to.
A : Type
A = FileHandle Append

||| A file can be read and written to.
RW : Type
RW = FileHandle ReadWrite

||| A file opened for reading and writing and has been truncated to
||| zero if it previsiouly existed.
RWPlus : Type
RWPlus = FileHandle ReadWriteTruncate

||| A file will read from the beginning and write at the end.
APlus : Type
APlus = FileHandle ReadAppend

-- --------------------------------------------------------------------- [ API ]

-- -------------------------------------------------------- [ Open/Close/Query ]

||| Open a file.
|||
||| @ fname the filename.
||| @ m     the mode; either Read, WriteTruncate, Append, ReadWrite,
|||         ReadWriteTruncate, or ReadAppend
|||
open : (fname : String)
    -> (m : Mode)
    -> Eff (FileOpSuccess)
           [FILE ()]
           (\res => [FILE (calcResourceTy m res)])
open f m = call $ Open f m

||| Open a file using C11 extended modes.
|||
||| @ fname the filename
||| @ m     the mode; either Read, WriteTruncate, Append, ReadWrite,
|||         ReadWriteTruncate, or ReadAppend
openX : (fname : String)
     -> (m : Mode)
     -> Eff (FileOpSuccess)
            [FILE ()]
            (\res => [FILE (calcResourceTy m res)])
openX f m = call $ OpenX f m

||| Close a file.
close : Eff () [FILE (FileHandle m)] [FILE ()]
close = call (Close)

||| Have we reached the end of the file.
eof : {auto prf : ValidModeRead m}
    -> Eff Bool [FILE (FileHandle m)]
eof = call FEOF

flush : Eff () [FILE (FileHandle m)]
flush = call FFlush

-- -------------------------------------------------------------------- [ Read ]

||| Read a `Char`.
readChar : {auto prf : ValidModeRead m}
      -> Eff (FileOpResult Char)
             [FILE (FileHandle m)]
readChar = call FGetC

||| Read a complete line.
readLine : {auto prf : ValidModeRead m}
        -> Eff (FileOpResult String)
               [FILE (FileHandle m)]
readLine = call FGetLine

-- ------------------------------------------------------------------- [ Write ]

||| Write a string to the file.
writeString : (str : String)
           -> {auto prf : ValidModeWrite m}
           -> Eff (FileOpSuccess)
                  [FILE (FileHandle m)]
writeString str = call $ FPutStr str

||| Write a complete line to the file.
writeLine : (str : String)
         -> {auto prf : ValidModeWrite m}
         -> Eff (FileOpSuccess)
                [FILE (FileHandle m)]
writeLine str = call $ FPutStrLn str

-- -------------------------------------------------------------- [ Whole File ]

||| Read the contents of a file into a string.
|||
||| This checks the size of
||| the file before beginning to read, and only reads that many bytes,
||| to ensure that it remains a total function if the file is appended
||| to while being read.
|||
||| Returns an error if fname is not a normal file.
readFile : (fname : String)
        -> Eff (FileOpResult String)
               [FILE ()]
readFile fn = call $ FReadFile fn

||| Create a file and write contents to the file.
writeFile : (fname    : String)
         -> (contents : String)
         -> Eff (FileOpSuccess)
                [FILE ()]
writeFile fn str = call $ FWriteFile fn str

-- --------------------------------------------------------------------- [ EOF ]
