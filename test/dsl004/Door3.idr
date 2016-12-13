import IOu

%language UniquenessTypes

data DoorState = OPEN | CLOSED

data DoorH : DoorState -> UniqueType where
     MkDH : DoorH s

infix 5 @@

data Res : (a : AnyType) -> (a -> AnyType) -> AnyType where
     (@@) : {k : a -> AnyType} -> (val : a) -> k val -> Res a k

data DoorCmd : AnyType -> AnyType where
     Open : DoorH CLOSED -> 
            DoorCmd (Res Bool (\ok => if ok then DoorH OPEN
                                            else DoorH CLOSED))
     Knock : DoorH CLOSED -> DoorCmd (DoorH CLOSED)
     Close : DoorH OPEN -> DoorCmd (DoorH CLOSED)

data DoorLang : AnyType -> AnyType where
     Pure : {a : AnyType} -> a -> DoorLang a
     Action : DoorCmd a -> DoorLang a
     (>>=) : DoorLang a -> (a -> DoorLang b) -> DoorLang b

testProg : DoorH CLOSED -> DoorLang (DoorH CLOSED)
testProg h = do h <- Action (Knock h)
                (True @@ h) <- Action (Open h) 
                   | (False @@ h) => Pure h
                Action (Close h)

