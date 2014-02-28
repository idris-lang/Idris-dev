module JavaScript

%access public

private
isUndefined : Ptr -> IO Bool
isUndefined p = do
  res <- mkForeign (
    FFun "%0 === undefined" [FPtr] FString) p
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
  mkForeign (FFun "%0.textContent=%1" [FPtr, FString] FUnit) p s


setOnClick : Element -> (Event -> IO Bool) -> IO ()
setOnClick (MkElem e) f =
  mkForeign (
    FFun "%0['onclick']=%1" [ FPtr
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
  e <- mkForeign (FFun "%0.item(%1)" [FPtr, FInt] FPtr) p (
    prim__truncBigInt_Int (cast i)
  )
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
    FFun "setInterval(%0,%1)" [FFunction FUnit (FAny (IO ())), FFloat64] FPtr
  ) f t
  return (MkInterval e)

clearInterval : Interval -> IO ()
clearInterval (MkInterval p) =
  mkForeign (FFun "clearInterval(%0)" [FPtr] FUnit) p

--------------------------------------------------------------------------------
-- Timeouts
--------------------------------------------------------------------------------
data Timeout : Type where
  MkTimeout : Ptr -> Timeout

setTimeout : (() -> IO ()) -> Float -> IO Timeout
setTimeout f t = do
  e <- mkForeign (
    FFun "setTimeout(%0,%1)" [FFunction FUnit (FAny (IO ())), FFloat64] FPtr
  ) f t
  return (MkTimeout e)

clearTimeout : Timeout -> IO ()
clearTimeout (MkTimeout p) =
  mkForeign (FFun "clearTimeout(%0)" [FPtr] FUnit) p

--------------------------------------------------------------------------------
-- Basic IO
--------------------------------------------------------------------------------
alert : String -> IO ()
alert msg =
  mkForeign (FFun "alert(%0)" [FString] FUnit) msg

--------------------------------------------------------------------------------
-- DOM
--------------------------------------------------------------------------------
query : String -> IO NodeList
query q = do
  e <- mkForeign (FFun "document.querySelectorAll(%0)" [FString] FPtr) q
  return (MkNodeList e)
