-- -------------------------------------------------------- [ Effectful FileIO ]
module Effect.File

import Effects
import Control.IOExcept

%access public

||| A Dependent type to describe File Handles. File handles are
||| parameterised with the current state of the file: Closed; Open for
||| reading; and Open for writing.
|||
||| @ m The file mode.
data OpenFile : (m : Mode) -> Type where
     FH : File -> OpenFile m

openOK : Mode -> Bool -> Type
openOK m True = OpenFile m
openOK m False = ()

-- ------------------------------------------------------------ [ The Protocol ]

||| Here the protocol for resource access is defined as an effect.
||| The state transitions diagram for the protocol is as follows:
|||
|||     digraph G {
|||
|||       empty; read; write; // States
|||
|||       empty -> read [label="Open R"];
|||       read -> empty [label="Close"];
|||       read -> read [label="ReadLine"];
|||       read -> read [label="EOF"];
|||
|||       empty -> write [label="Open W"];
|||       write -> empty [label="Close"];
|||       write -> write [label="WriteLine"];
|||
|||     }
data FileIO : Effect where
  ||| Open a file with the specified mode.
  |||
  ||| Opening a file successful moves the state from 'empty' to the
  ||| specified mode. If not successful the state is still 'empty'.
  |||
  ||| @ fname The file name to be opened.
  ||| @ m The file mode.
  Open : (fname: String)
         -> (m : Mode)
         -> sig FileIO Bool () (\res => case res of
                                             True => OpenFile m
                                             False => ())

  ||| Close a file.
  |||
  ||| Closing a file moves the state from Open to closed.
  Close : sig FileIO () (OpenFile m) ()

  ||| Read a line from the file.
  |||
  ||| Only files that are open for reading can be read.
  ReadLine : sig FileIO String (OpenFile Read)

  ||| Write a string to a file.
  |||
  ||| Only file that are open for writing can be written to.
  WriteString : String -> sig FileIO () (OpenFile Write)

  ||| End of file?
  |||
  ||| Only files open for reading can be tested for EOF
  EOF : sig FileIO Bool (OpenFile Read)

-- ------------------------------------------------------------ [ The Handlers ]

--- An implementation of the resource access protocol for the IO Context.
implementation Handler FileIO IO where
    handle () (Open fname m) k = do Right h <- openFile fname m
                                        | Left err => k False ()
                                    k True (FH h)
    handle (FH h) Close      k = do closeFile h
                                    k () ()
    handle (FH h) ReadLine        k = do Right str <- fGetLine h
                                         -- Need proper error handling!
                                             | Left err => k "" (FH h)
                                         k str (FH h)
    handle (FH h) (WriteString str) k = do Right () <- fPutStr h str
                                             | Left err => k () (FH h)
                                           k () (FH h)
    handle (FH h) EOF             k = do e <- fEOF h
                                         k e (FH h)

implementation Handler FileIO (IOExcept a) where
    handle () (Open fname m) k = do Right h <- ioe_lift $ openFile fname m
                                        | Left err => k False ()
                                    k True (FH h)
    handle (FH h) Close      k = do ioe_lift $ closeFile h
                                    k () ()
    handle (FH h) ReadLine        k = do Right str <- ioe_lift $ fGetLine h
                                         -- Need proper error handling!
                                             | Left err => k "" (FH h)
                                         k str (FH h)
    handle (FH h) (WriteString str) k = do Right () <- ioe_lift $ fPutStr h str
                                             | Left err => k () (FH h)
                                           k () (FH h)
    handle (FH h) EOF             k = do e <- ioe_lift $ fEOF h
                                         k e (FH h)

-- -------------------------------------------------------------- [ The Effect ]
FILE_IO : Type -> EFFECT
FILE_IO t = MkEff t FileIO

-- ------------------------------------------------------------ [ The Bindings ]
--
-- Bind the IO context handlers to functions. These functions will run
-- in the IO context.
--

||| Open a file with the specified mode.
|||
||| @ fname The file name to be opened.
||| @ m The file mode.
open : (fname : String)
       -> (m : Mode)
       -> Eff Bool [FILE_IO ()]
                   (\res => [FILE_IO (case res of
                                           True => OpenFile m
                                           False => ())])
open f m = call $ Open f m


||| Close a file.
close : Eff () [FILE_IO (OpenFile m)] [FILE_IO ()]
close = call $ Close

||| Read a line from the file.
readLine : Eff String [FILE_IO (OpenFile Read)]
readLine = call $ ReadLine

||| Write a string to a file.
writeString : String -> Eff () [FILE_IO (OpenFile Write)]
writeString str = call $ WriteString str

||| Write a line to a file.
writeLine : String -> Eff () [FILE_IO (OpenFile Write)]
writeLine str = call $ WriteString (str ++ "\n")

||| End of file?
eof : Eff Bool [FILE_IO (OpenFile Read)]
eof = call $ EOF

||| Read a complete file, returning a user defined error if
||| unsuccesful.
|||
readFile : (errFunc : String -> e)
        -> (fname   : String)
        -> Eff (Either e String) [FILE_IO ()]
readFile errFunc fname = do
    case !(open fname Read) of
      False => pure $ Left (errFunc fname)
      True => do
        src <- readAcc ""
        close
        pure $ Right src
  where
    readAcc : String -> Eff String [FILE_IO (OpenFile Read)]
    readAcc acc = if (not !(eof))
                     then readAcc (acc ++ !(readLine))
                     else pure acc

||| Write a file containing the provided string, returning a user
||| defined error if unsuccesful.
|||
writeFile : (errFunc : String -> e)
         -> (fname   : String)
         -> (content : String)
         -> Eff (Either e ()) [FILE_IO ()]
writeFile errFunc fname content = do
    case !(open fname Write) of
      True => do
        writeString content
        close
        pure $ Right ()
      False => pure $ Left (errFunc fname)


namespace Default
  readFile : String -> Eff (Either String String) [FILE_IO ()]
  readFile = File.readFile id

  writeFile : String -> String -> Eff (Either String ()) [FILE_IO ()]
  writeFile = File.writeFile id
-- --------------------------------------------------------------------- [ EOF ]
