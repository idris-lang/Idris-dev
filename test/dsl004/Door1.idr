import IOu

import Data.Vect

%language UniquenessTypes

data Result : (a : AnyType) -> (a -> AnyType) -> AnyType where
     Res : {k : a -> AnyType} -> (val : a) -> (h : k val) -> Result a k





------
data DoorState = OPEN | CLOSED

data DoorH : DoorState -> UniqueType where
     MkDH : DoorH s

data DoorCmd : AnyType -> AnyType where
     Open : DoorH CLOSED -> DoorCmd (DoorH OPEN)
     Knock : DoorH CLOSED -> DoorCmd (DoorH CLOSED)
     Close : DoorH OPEN -> DoorCmd (DoorH CLOSED)

data DoorLang : AnyType -> AnyType where
     Pure : {a : AnyType} -> a -> DoorLang a
     Action : DoorCmd a -> DoorLang a
     (>>=) : DoorLang a -> (a -> DoorLang b) -> DoorLang b

implicit
action : DoorCmd a -> DoorLang a
action = Action

testProg : DoorH CLOSED -> DoorLang ()
testProg h = with Main, Show do -- h <- Knock h
                h <- Open h
                -- h <- Close h
                Pure ()

