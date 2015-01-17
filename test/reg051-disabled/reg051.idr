-- Test for problem with parameter propagation in fromState'

data StateTy : Type where
    STInt    : StateTy
    STString : StateTy
    STMaybe  : StateTy -> StateTy
    STList   : StateTy -> StateTy

interpSTy : StateTy -> Type
interpSTy STInt       = Int
interpSTy STString    = String
interpSTy (STMaybe a) = Maybe (interpSTy a)
interpSTy (STList  a) = List  (interpSTy a)

data State : StateTy -> Type where
  MkState : (t : StateTy) -> Ptr -> State t

abstract
data StateC : StateTy -> Type where
  MkStateC : Int -> (t : StateTy) -> Ptr -> StateC t

isObj : Ptr -> IO Bool
isObj p = do
  "object" <- mkForeign (FFun "typeof %0" [FPtr] FString) p
    | _ => pure False
  pure True

stateVarName : String
stateVarName = "__IDR__IQUERY__STATE__"

stateVarExists : IO Bool
stateVarExists = do
  o <- mkForeign (FFun ("typeof " ++ stateVarName) [] FString) 
  pure $ if o == "object" then True else False

initStateVar : IO Ptr
initStateVar = mkForeign (FFun (stateVarName ++ " = {count: 0}") [] FPtr)

getStateVar : IO (Maybe Ptr) 
getStateVar = case !stateVarExists of
  True  => map Just $ mkForeign (FFun stateVarName [] FPtr)
  False => pure Nothing

getStateVar' : IO Ptr
getStateVar' = case !getStateVar of
  Just s  => pure s
  Nothing => initStateVar

stateCExists : Ptr -> Int -> IO Bool
stateCExists c n = do
  r <- mkForeign (FFun "typeof %0[%1]" [FPtr,FInt] FString) c n
  pure $ if r == "object" then True else False

incCount : Ptr -> IO Int
incCount c = do
  n <- mkForeign (FFun "%0.count" [FPtr] FInt) c
  mkForeign (FFun "%0.count++" [FPtr] FUnit) c
  pure n

infixl 5 =>>
public
(=>>) : IO (Maybe (State a)) -> (State a -> IO (Maybe b)) 
                             -> IO (Maybe b)
s =>> f = do
  (Just s') <- s
    | Nothing => pure Nothing
  f s'

infixl 5 :=>
public
(:=>) : IO (Maybe (State a)) -> (State a -> IO ()) -> IO Bool
(:=>) s f = do
  (Just s') <- s
    | Nothing => pure False
  f s'
  pure True

public 
access : Nat -> State (STList t) -> IO (Maybe (State t))
access n (MkState (STList t) p) = do
  r <- mkForeign (FFun "%0.val[%1]" [FPtr,FInt] FPtr) p (fromNat n)
  True <- isObj r
    | False => pure Nothing
  pure $ Just $ MkState t r

fromState' : State t -> IO (interpSTy t)
fromState' (MkState STInt p) = mkForeign (FFun "%0.val" [FPtr] FInt) p
fromState' (MkState STString    p) = mkForeign (FFun "%0.val" [FPtr] FString) p
fromState' (MkState (STMaybe a) p) = do
  isNull <- (mkForeign (FFun "(%0.val == null).toString()" [FPtr] FString) p) 
  case isNull == "true" of
    True  => pure Nothing
    False => pure $ Just !(fromState' (MkState a p))
fromState' (MkState (STList a) p) = do
  n <- mkForeign (FFun "%0.val.length" [FPtr] FInt) p
  ps <- sequence $ map 
     (\n => mkForeign (FFun "%0.val[%1]" [FPtr,FInt] FPtr) p n) [0..(n-1)]
  sequence $ map (\p' => fromState' (MkState a p')) ps

