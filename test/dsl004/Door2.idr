import IOu

%language UniquenessTypes

data DoorState = OPEN | CLOSED

data DoorH : DoorState -> UniqueType where
     MkDH : DoorH s

infix 5 @@

data Res : (a : AnyType) -> (a -> AnyType) -> AnyType where
     (@@) : (val : a) -> (h : k val) -> Res a k

data DoorCmd : AnyType -> AnyType where
     Open : DoorH CLOSED -> 
            DoorCmd (Res Bool (\ok => case ok of
                                        True => DoorH OPEN
                                        False => DoorH CLOSED))
     Knock : DoorH CLOSED -> DoorCmd (DoorH CLOSED)
     Close : DoorH OPEN -> DoorCmd (DoorH CLOSED)

data DoorLang : AnyType -> AnyType where
     Pure : a -> DoorLang a
     Action : DoorCmd a -> DoorLang a
     (>>=) : DoorLang a -> (a -> DoorLang b) -> DoorLang b

implicit
action : DoorCmd a -> DoorLang a
action = Action

covering
testProg : DoorH CLOSED -> DoorLang ()
testProg h = do h <- Action (Knock h)
                (True @@ h) <- Action (Open h) 
                     | (False @@ h) => testProg h 
                h <- Action (Close h)
                Pure ()

