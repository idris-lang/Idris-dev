module Control.ST.File 

import Control.ST
import Control.IOExcept

%default total

||| A record of the file modes that can read from a file.
public export
data ValidModeRead : Mode -> Type where
  VMRRead   : ValidModeRead Read
  VMRReadW  : ValidModeRead ReadWrite
  VMRReadWT : ValidModeRead ReadWriteTruncate
  VMRReadA  : ValidModeRead ReadAppend

||| A record of the file modes that can write from a file.
public export
data ValidModeWrite : Mode -> Type where
  VMWWrite  : ValidModeWrite WriteTruncate
  VMWAppend : ValidModeWrite Append
  VMWReadW  : ValidModeWrite ReadWrite
  VMWReadWT : ValidModeWrite ReadWriteTruncate

||| The file handle which will be used as a State Transition 
||| resource in the `IO` and `IOExcept` implementations of `File`.
|||
||| @mode The `Mode` that the handle was generated under.
|||
public export
data FileHandle : (mode : Mode) -> Type where
  FH : File -> FileHandle mode

||| Description of state transition operations on a file.
|||
||| +------------+-------------+----------------+----------------+----------------+
||| | Operation  | State in    | Mode in        | State out      | Mode out       |
||| +------------+-------------+----------------+----------------+----------------+
||| | open       | -           | -              | file handle    | input paramater|
||| | close      | file handle | any            | -              | -              |
||| | eof        | file handle | ValidModeRead  | file handle    | ValidModeRead  |
||| | flush      | file handle | any            | file handle    | unchanged      |
||| | readLine   | file handle | ValidModeRead  | file handle    | ValidModeRead  |
||| | readChar   | file handle | ValidModeRead  | file handle    | ValidModeRead  |
||| | readFile   | -           | -              | -              | -              |
||| | writeString| file handle | ValidModeWrite | file handle    | ValidModeWrite |
||| | writeLine  | file handle | ValidModeWrite | file handle    | ValidModeWrite |
||| | writeFile  | -           | -              | -              | -              |
||| +------------+-------------+----------------+----------------+----------------+
|||
public export
interface File (m : Type -> Type) where
  FileHandleI : Mode -> Type

  ||| Open a file.
  |||
  ||| @fname the filename.
  ||| @mode  the mode; either Read, WriteTruncate, Append, ReadWrite,
  |||        ReadWriteTruncate, or ReadAppend
  |||
  open     :  (fname : String)
           -> (mode  : Mode)
           -> ST m (Either FileError Var) [ addIfRight (FileHandleI mode) ]

  ||| Close a file.
  close    :  (fileHandle : Var)
           -> ST m () [ remove fileHandle (FileHandleI mode)  ]

  ||| Have we reached the end of the file.
  eof      :  (fileHandle : Var)
           -> {auto prf   : ValidModeRead mode}
           -> ST m Bool [ fileHandle ::: (FileHandleI mode) ]

  ||| Flush
  flush    :  (fileHandle : Var)
           -> ST m () [ fileHandle ::: (FileHandleI mode) ]

  ||| Read a complete line.
  readLine :  (fileHandle : Var)
           -> {auto prf   : ValidModeRead mode}
           -> ST m (Either FileError String) [ fileHandle ::: (FileHandleI mode) ]

  ||| Read a `Char`.
  readChar :  (fileHandle : Var)
           -> {auto prf   : ValidModeRead mode}
           -> ST m (Either FileError Char) [ fileHandle ::: (FileHandleI mode) ]

  ||| Read the contents of a file into a string.
  |||
  ||| This checks the size of
  ||| the file before beginning to read, and only reads that many bytes,
  ||| to ensure that it remains a total function if the file is appended
  ||| to while being read.
  |||
  ||| Returns an error if fname is not a normal file.
  |||
  readFile :  (fileName : String)
           -> ST m (Either FileError String) []

  ||| Write a complete line to the file.
  |||
  ||| @string The string to be written to file.
  |||
  writeString : (fileHandle : Var)
           -> (string     : String) 
           -> {auto prf   : ValidModeWrite mode}
           -> ST m (Either FileError ()) [ fileHandle ::: (FileHandleI mode) ]

  ||| Write a complete line to the file.
  |||
  ||| @string The text to be written to file.
  |||
  writeLine : (fileHandle : Var)
           -> (string     : String) 
           -> {auto prf   : ValidModeWrite mode}
           -> ST m (Either FileError ()) [ fileHandle ::: (FileHandleI mode) ]

  ||| Create a file and write contents to the file.
  |||
  ||| @fname  The fileName of the file.
  ||| @string The text to be written to file.
  |||
  writeFile : (fname  : String)
           -> (string : String)
           -> ST m (Either FileError ()) []

public export
File IO where
  FileHandleI mode = State (FileHandle mode) 

  open fname mode = do 
      (Right file) <- lift ( openFile fname mode )
                   | (Left  error ) => pure (Left error)
      let fh = FH file
      var <- new fh 
      pure (Right var)

  close fh = do 
      (FH file) <- read fh
      lift (closeFile file)
      delete fh 
      pure ()

  eof fh = do  
      (FH file) <- read fh 
      isEof <- lift (fEOF file)
      pure (isEof)

  flush fh = do 
      (FH file) <- read fh 
      lift (fEOF file)
      pure ()

  readLine fh = do 
      (FH file) <- read fh 
      (Right string) <- lift (fGetLine file)
                     | (Left  error ) => pure (Left error) 
      pure (Right string)

  readChar fh = do 
      (FH file) <- read fh 
      (Right chr) <- lift (fgetc file)
                  | (Left  error ) => pure (Left error) 
      pure (Right chr)

  readFile fname = do
      (Right content) <- lift ( readFile fname )
                      | (Left  error ) => pure (Left error) 
      pure (Right content)

  writeString fh str = do 
      (FH file) <- read fh 
      Right x <- lift (fPutStr file str)
              | (Left  error ) => pure (Left error) 
      pure (Right x)

  writeLine fh str = do 
      (FH file) <- read fh
      Right x <- lift (fPutStrLn file str)
              | (Left  error ) => pure (Left error) 
      pure (Right x)

  writeFile fname str = do
      Right x <- lift (writeFile fname str)
              | (Left error ) => pure (Left error) 
      pure (Right x)

public export
File (IOExcept a) where
  FileHandleI mode = State (FileHandle mode) 

  open fname mode = do 
      (Right file) <- lift (ioe_lift (openFile fname mode))
                   | (Left  error ) => pure (Left error)
      let fh = FH file
      var <- new fh 
      pure (Right var)

  close fh = do 
      (FH file) <- read fh
      lift (ioe_lift (closeFile file))
      delete fh 
      pure ()

  eof fh = do  
      (FH file) <- read fh 
      isEof <- lift (ioe_lift (fEOF file))
      pure (isEof)

  flush fh = do 
      (FH file) <- read fh 
      lift (ioe_lift (fEOF file))
      pure ()

  readLine fh = do 
      (FH file) <- read fh 
      (Right string) <- lift (ioe_lift (fGetLine file))
                     | (Left  error ) => pure (Left error) 
      pure (Right string)

  readChar fh = do 
      (FH file) <- read fh 
      (Right chr) <- lift (ioe_lift (fgetc file))
                  | (Left  error ) => pure (Left error) 
      pure (Right chr)

  readFile fname = do
      (Right content) <- lift (ioe_lift (readFile fname))
                      | (Left  error ) => pure (Left error) 
      pure (Right content)

  writeString fh str = do 
      (FH file) <- read fh 
      Right x <- lift (ioe_lift (fPutStr file str))
              | (Left  error ) => pure (Left error) 
      pure (Right x)

  writeLine fh str = do 
      (FH file) <- read fh
      Right x <- lift (ioe_lift (fPutStrLn file str))
              | (Left  error ) => pure (Left error) 
      pure (Right x)

  writeFile fname str = do
      Right x <- lift (ioe_lift (writeFile fname str))
              | (Left error ) => pure (Left error) 
      pure (Right x)
--- EOF -------------------------------------------------------------------------
