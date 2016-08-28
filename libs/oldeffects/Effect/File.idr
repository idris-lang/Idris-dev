-- -------------------------------------------------------- [ Effectful FileIO ]
module Effect.File

import Effects
import Control.IOExcept


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
         -> {() ==> {res} if res
                             then OpenFile m
                             else ()} FileIO Bool

  ||| Close a file.
  ||| 
  ||| Closing a file moves the state from Open to closed.
  Close : {OpenFile m ==> ()} FileIO () 

  ||| Read a line from the file.
  ||| 
  ||| Only files that are open for reading can be read.
  ReadLine : {OpenFile Read}  FileIO String 
  
  ||| Write a line to a file.
  ||| 
  ||| Only file that are open for writing can be written to.
  WriteLine : String -> {OpenFile Write} FileIO ()

  ||| End of file?
  ||| 
  ||| Only files open for reading can be tested for EOF
  EOF : {OpenFile Read}  FileIO Bool

-- ------------------------------------------------------------ [ The Handlers ]

--- An implementation of the resource access protocol for the IO Context.
implementation Handler FileIO IO where
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
       -> { [FILE_IO ()] ==> [FILE_IO (if result
                                          then OpenFile m
                                          else ())] } Eff e Bool
open f m = call $ Open f m


||| Close a file.
close : { [FILE_IO (OpenFile m)] ==> [FILE_IO ()] } Eff e ()
close = call $ Close

||| Read a line from the file.
readLine : { [FILE_IO (OpenFile Read)] } Eff e String 
readLine = call $ ReadLine

||| Write a line to a file.
writeLine : String -> { [FILE_IO (OpenFile Write)] } Eff e ()
writeLine str = call $ WriteLine str

||| End of file?
eof : { [FILE_IO (OpenFile Read)] } Eff e Bool 
eof = call $ EOF

-- --------------------------------------------------------------------- [ EOF ]
