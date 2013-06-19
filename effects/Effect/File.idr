module Effect.File

import Effects
import Control.IOExcept
import Decidable.Decidable

data OpenFile : Mode -> Type where
     FH : File -> OpenFile m

class AllowsRead (m : Mode) where
  notWriteOnly : (m = Write) -> _|_

instance AllowsRead Read where
  notWriteOnly refl impossible
instance AllowsRead ReadWrite where
  notWriteOnly refl impossible

class AllowsWrite (m : Mode) where
  notReadOnly : (m = Read) -> _|_

instance AllowsWrite Write where
  notReadOnly refl impossible
instance AllowsWrite ReadWrite where
  notReadOnly refl impossible


data FileIO : Effect where
     Open  : String -> (m : Mode)   -> FileIO () (OpenFile m) ()
     Close :                           FileIO (OpenFile m) () ()

     ReadLine  : AllowsRead mode    => FileIO (OpenFile m) (OpenFile m) String
     WriteLine : AllowsWrite mode   =>
                 String             -> FileIO (OpenFile m) (OpenFile m) ()
     EOF       : AllowsRead mode    => FileIO (OpenFile m) (OpenFile m) Bool
     GetLength : AllowsRead mode    => FileIO (OpenFile m) (OpenFile m) Nat
     GetHandle :                       FileIO (OpenFile m) (OpenFile m) File

instance Handler FileIO IO where
    handle () (Open fname m) k = do h <- openFile fname m
                                    k (FH h) ()
    handle (FH h) Close      k = do closeFile h
                                    k () ()
    handle (FH h) (ReadLine)      k = do str <- fread h
                                         k (FH h) str
    handle (FH h) (WriteLine str) k = do fwrite h str
                                         k (FH h) ()
    handle (FH h) (EOF)           k = do e <- feof h
                                         k (FH h) e
    handle (FH h) (GetLength)     k = do l <- fileLength h
                                         k (FH h) l
    handle (FH h) (GetHandle)     k = do k (FH h) h

instance Handler FileIO (IOExcept String) where
    handle () (Open fname m) k 
       = do h <- ioe_lift (openFile fname m)
            valid <- ioe_lift (validFile h)
            if valid then k (FH h) ()
                     else ioe_fail "File open failed"
    handle (FH h) Close             k = do ioe_lift (closeFile h); k () ()
    handle (FH h) (ReadLine)      k = do str <- ioe_lift (fread h)
                                         k (FH h) str
    handle (FH h) (WriteLine str) k = do ioe_lift (fwrite h str)
                                         k (FH h) ()
    handle (FH h) (EOF)           k = do e <- ioe_lift (feof h)
                                         k (FH h) e
    handle (FH h) (GetLength)     k = do l <- ioe_lift (fileLength h)
                                         k (FH h) l
    handle (FH h) (GetHandle)     k = do k (FH h) h

FILE_IO : Type -> EFFECT
FILE_IO t = MkEff t FileIO 

open : Handler FileIO e =>
       String -> (m : Mode) -> EffM e [FILE_IO ()] [FILE_IO (OpenFile m)] ()
open f m = Open f m

close : Handler FileIO e =>
        EffM e [FILE_IO (OpenFile m)] [FILE_IO ()] ()
close = Close

readLine : (Handler FileIO e, AllowsRead mode) =>
           Eff e [FILE_IO (OpenFile mode)] String
readLine = ReadLine

writeLine : (Handler FileIO e, AllowsWrite mode) =>
            String -> Eff e [FILE_IO (OpenFile mode)] ()
writeLine str = WriteLine str

eof : (Handler FileIO e, AllowsRead mode) =>
      Eff e [FILE_IO (OpenFile mode)] Bool
eof = EOF

getHandle : Handler FileIO e =>
            Eff e [FILE_IO (OpenFile mode)] File
getHandle = GetHandle

getLength : (Handler FileIO e, AllowsRead mode) =>
            Eff e [FILE_IO (OpenFile mode)] Nat
getLength = GetLength


