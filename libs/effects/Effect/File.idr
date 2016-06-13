module Effect.File

import Effects
import Control.IOExcept

%access public export

-- -------------------------------------------------------------- [ Predicates ]

data ValidModeRead : Mode -> Type where
  VMRRead   : ValidModeRead Read
  VMRReadW  : ValidModeRead ReadWrite
  VMRReadWT : ValidModeRead ReadWriteTruncate
  VMRReadA  : ValidModeRead ReadAppend

data ValidModeWrite : Mode -> Type where
  VMWWrite  : ValidModeWrite WriteTruncate
  VMWAppend : ValidModeWrite Append
  VMWReadW  : ValidModeWrite ReadWrite
  VMWReadWT : ValidModeWrite ReadWriteTruncate


-- -------------------------------------------------- [ Custom Error Reporting ]

namespace FileResult

  data ResultDesc = SUCCESS | RESULT

  data FileOpReturnTy : ResultDesc -> Type -> Type where
    Success : FileOpReturnTy SUCCESS a
    Result  : a ->  FileOpReturnTy RESULT a
    FError  : FileError -> FileOpReturnTy ty a

  FileOpResult : Type -> Type
  FileOpResult ty = FileOpReturnTy RESULT ty

  FileOpSuccess : Type
  FileOpSuccess = FileOpReturnTy SUCCESS ()

-- ------------------------------------------------------------ [ The Resource ]

data FileHandle : (m : Mode) -> Type where
    FH : File -> FileHandle m

-- ---------------------------------------------- [ Resource Type Construction ]

calcResourceTy : (m : Mode)
              -> FileOpReturnTy fOpTy retTy
              -> Type
calcResourceTy _ (FError e) = ()
calcResourceTy m _          = FileHandle m

-- ------------------------------------------------------- [ Effect Definition ]
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

  -- Query
  handle (FH fh) FEOF k = do
      res <- ioe_lift $ fEOF fh
      k res (FH fh)

-- ------------------------------------------------------ [ Effect and Helpers ]

FILE : Type -> EFFECT
FILE t = MkEff t FileE

R : Type
R = FileHandle Read

W : Type
W = FileHandle WriteTruncate

A : Type
A = FileHandle Append

RW : Type
RW = FileHandle ReadWrite

RWPlus : Type
RWPlus = FileHandle ReadWriteTruncate

APlus : Type
APlus = FileHandle ReadAppend

-- --------------------------------------------------------------------- [ API ]

-- -------------------------------------------------------- [ Open/Close/Query ]


open : (fname : String)
    -> (m : Mode)
    -> Eff (FileOpSuccess)
           [FILE ()]
           (\res => [FILE (calcResourceTy m res)])
open f m = call $ Open f m

openX : (fname : String)
     -> (m : Mode)
     -> Eff (FileOpSuccess)
            [FILE ()]
            (\res => [FILE (calcResourceTy m res)])
openX f m = call $ OpenX f m

close : Eff () [FILE (FileHandle m)] [FILE ()]
close = call (Close)

eof : {auto prf : ValidModeRead m}
    -> Eff Bool [FILE (FileHandle m)]
eof = call FEOF


-- -------------------------------------------------------------------- [ Read ]

readChar : {auto prf : ValidModeRead m}
      -> Eff (FileOpResult Char)
             [FILE (FileHandle m)]
readChar = call FGetC

readLine : {auto prf : ValidModeRead m}
        -> Eff (FileOpResult String)
               [FILE (FileHandle m)]
readLine = call FGetLine

-- ------------------------------------------------------------------- [ Write ]

writeString : (str : String)
           -> {auto prf : ValidModeWrite m}
           -> Eff (FileOpSuccess)
                  [FILE (FileHandle m)]
writeString str = call $ FPutStr str

writeLine : (str : String)
         -> {auto prf : ValidModeWrite m}
         -> Eff (FileOpSuccess)
                [FILE (FileHandle m)]
writeLine str = call $ FPutStrLn str

-- -------------------------------------------------------------- [ Whole File ]

readFile : (fname : String)
        -> Eff (FileOpResult String)
               [FILE ()]
readFile fn = call $ FReadFile fn

writeFile : (fname    : String)
         -> (contents : String)
         -> Eff (FileOpSuccess)
                [FILE ()]
writeFile fn str = call $ FWriteFile fn str

-- --------------------------------------------------------------------- [ EOF ]
