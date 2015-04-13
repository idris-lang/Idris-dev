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
instance Handler FileIO IO where
    handle () (Open fname m) k = do h <- openFile fname m
                                    valid <- validFile h
                                    if valid then k True (FH h) 
                                             else k False ()
    handle (FH h) Close      k = do closeFile h
                                    k () ()
    handle (FH h) ReadLine        k = do str <- fread h
                                         k str (FH h)
    handle (FH h) (WriteString str) k = do fwrite h str
                                           k () (FH h)
    handle (FH h) EOF             k = do e <- feof h
                                         k e (FH h)

instance Handler FileIO (IOExcept a) where
    handle () (Open fname m) k = do h <- ioe_lift $ openFile fname m
                                    valid <- ioe_lift $ validFile h
                                    if valid then k True (FH h)
                                             else k False ()
    handle (FH h) Close      k = do ioe_lift $ closeFile h
                                    k () ()
    handle (FH h) ReadLine        k = do str <- ioe_lift $ fread h
                                         k str (FH h)
    handle (FH h) (WriteString str) k = do ioe_lift $ fwrite h str
                                           k () (FH h)
    handle (FH h) EOF             k = do e <- ioe_lift $ feof h
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

-- --------------------------------------------------------------------- [ EOF ]
