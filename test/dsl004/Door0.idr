import IOu

data Result : (a : Type) -> (a -> Type) -> Type* where
     Res : {k : a -> Type} -> (val : a) -> k val -> Result a k







------
data DoorState = OPEN | CLOSED

data DoorH : DoorState -> Type where
  MkDH : {s : DoorState} -> DoorH s

data DoorCmd : Type -> Type where
     Open : DoorH CLOSED -> DoorCmd (DoorH OPEN)
     Knock : DoorH CLOSED -> DoorCmd (DoorH CLOSED)
     Close : DoorH OPEN -> DoorCmd (DoorH CLOSED)

data DoorLang : Type -> Type where
     Return : a -> DoorLang a
     Action : DoorCmd a -> DoorLang a
     (>>=) : DoorLang a -> (a -> DoorLang b) -> DoorLang b

testProg : DoorH CLOSED -> DoorLang ()
testProg h = do h <- Action (Knock h)
                h <- Action (Open h)
                h <- Action (Close h)
                Return ()

