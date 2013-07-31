module JavaScript

%access public

-- TODO: Get rid of this hack, and find a better way.
private
isUndefined : Ptr -> UnsafeIO Bool
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

setText : Element -> String -> UnsafeIO ()
setText (MkElem p) s =
  mkForeign (FFun ".textContent=" [FPtr, FString] FUnit) p s


setOnClick : Element -> (Event -> UnsafeIO Bool) -> UnsafeIO ()
setOnClick (MkElem e) f =
  mkForeign (
    FFun "['onclick']=" [ FPtr
                        , FFunction (FAny Event) (FAny (UnsafeIO Bool))
                        ] FUnit) e f
--------------------------------------------------------------------------------
-- Nodelists
--------------------------------------------------------------------------------
abstract
data NodeList : Type where
  MkNodeList : Ptr -> NodeList

elemAt : NodeList -> Nat -> UnsafeIO (Maybe Element)
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

setInterval : (() -> UnsafeIO ()) -> Float -> UnsafeIO Interval
setInterval f t = do
  e <- mkForeign (
    FFun "setInterval" [FFunction FUnit (FAny (UnsafeIO ())), FFloat] FPtr) f t
  return (MkInterval e)

clearInterval : Interval -> UnsafeIO ()
clearInterval (MkInterval p) =
  mkForeign (FFun "clearInterval" [FPtr] FUnit) p

--------------------------------------------------------------------------------
-- Timeouts
--------------------------------------------------------------------------------
data Timeout : Type where
  MkTimeout : Ptr -> Timeout

setTimeout : (() -> UnsafeIO ()) -> Float -> UnsafeIO Timeout
setTimeout f t = do
  e <- mkForeign (
    FFun "setTimeout" [FFunction FUnit (FAny (UnsafeIO ())), FFloat] FPtr) f t
  return (MkTimeout e)

clearTimeout : Timeout -> UnsafeIO ()
clearTimeout (MkTimeout p) =
  mkForeign (FFun "clearTimeout" [FPtr] FUnit) p

--------------------------------------------------------------------------------
-- Basic UnsafeIO
--------------------------------------------------------------------------------
alert : String -> UnsafeIO ()
alert msg =
  mkForeign (FFun "alert" [FString] FUnit) msg

--------------------------------------------------------------------------------
-- DOM
--------------------------------------------------------------------------------
query : String -> UnsafeIO NodeList
query q = do
  e <- mkForeign (FFun "document.querySelectorAll" [FString] FPtr) q
  return (MkNodeList e)
