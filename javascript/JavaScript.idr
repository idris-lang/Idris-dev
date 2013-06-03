module JavaScript

%access public

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
-- Events
--------------------------------------------------------------------------------
abstract
data Event : Type where
  MkEvent : Ptr -> Event

--------------------------------------------------------------------------------
-- Nodelists
--------------------------------------------------------------------------------
abstract
data NodeList : Type where
  MkNodeList : Ptr -> NodeList

elemAt : NodeList -> Nat -> IO Element
elemAt (MkNodeList p) i = do
  i <- mkForeign (FFun ".item" [FPtr, FInt] FPtr) p (cast i)
  return (MkElem i)
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
