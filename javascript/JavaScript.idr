module JavaScript

%access public

-- TODO: Get rid of this hack, and find a better way.
private
isUndefined : Ptr -> IO Bool
isUndefined p = do
  res <- mkForeign (
    FFun "(function(arg) { return arg === undefined;})" [FPtr] FString) p
  if res == "false"
     then (return False)
     else (return True)

--------------------------------------------------------------------------------
-- Events
--------------------------------------------------------------------------------
abstract
data Event : Type where
  MkEvent : Ptr -> Event

--------------------------------------------------------------------------------
-- Elements
--------------------------------------------------------------------------------
abstract
data Element : Type where
  MkElem : Ptr -> Element

setText : Element -> String -> IO ()
setText (MkElem p) s =
  mkForeign (FFun ".textContent=" [FPtr, FString] FUnit) p s


setOnClick : Element -> (Event -> IO Bool) -> IO ()
setOnClick (MkElem e) f =
  mkForeign (
    FFun "['onclick']=" [ FPtr
                        , FFunction (FAny Event) (FAny (IO Bool))
                        ] FUnit) e f
--------------------------------------------------------------------------------
-- Nodelists
--------------------------------------------------------------------------------
abstract
data NodeList : Type where
  MkNodeList : Ptr -> NodeList

elemAt : NodeList -> Nat -> IO (Maybe Element)
elemAt (MkNodeList p) i = do
  e <- mkForeign (FFun ".item" [FPtr, FInt] FPtr) p (prim__truncBigInt_Int (cast i))
  d <- isUndefined e
  if d
     then return $ Just (MkElem e)
     else return Nothing

--------------------------------------------------------------------------------
-- Intervals
--------------------------------------------------------------------------------
abstract
data Interval : Type where
  MkInterval : Ptr -> Interval

setInterval : (() -> IO ()) -> Float -> IO Interval
setInterval f t = do
  e <- mkForeign (
    FFun "setInterval" [FFunction FUnit (FAny (IO ())), FFloat] FPtr) f t
  return (MkInterval e)

clearInterval : Interval -> IO ()
clearInterval (MkInterval p) =
  mkForeign (FFun "clearInterval" [FPtr] FUnit) p

--------------------------------------------------------------------------------
-- Timeouts
--------------------------------------------------------------------------------
data Timeout : Type where
  MkTimeout : Ptr -> Timeout

setTimeout : (() -> IO ()) -> Float -> IO Timeout
setTimeout f t = do
  e <- mkForeign (
    FFun "setTimeout" [FFunction FUnit (FAny (IO ())), FFloat] FPtr) f t
  return (MkTimeout e)

clearTimeout : Timeout -> IO ()
clearTimeout (MkTimeout p) =
  mkForeign (FFun "clearTimeout" [FPtr] FUnit) p

--------------------------------------------------------------------------------
-- Basic IO
--------------------------------------------------------------------------------
alert : String -> IO ()
alert msg =
  mkForeign (FFun "alert" [FString] FUnit) msg

--------------------------------------------------------------------------------
-- DOM
--------------------------------------------------------------------------------
query : String -> IO NodeList
query q = do
  e <- mkForeign (FFun "document.querySelectorAll" [FString] FPtr) q
  return (MkNodeList e)
