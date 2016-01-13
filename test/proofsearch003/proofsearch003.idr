import Data.Fin

data Wrapper = Wrap (Fin 9)

data Seq : Fin 9 -> Fin 9 -> Type where
  Seq12 : {n : Fin 8} -> Seq (weaken n) (FS n)
  Seq21 : {n : Fin 8} -> Seq (FS n) (weaken n)

interface Evil t where
  value : t -> Fin 9

implementation Evil Wrapper where
  value (Wrap n) = n

consTest : (Evil t) => (a : t) -> (b : t) -> 
           {auto p : Seq (value a) (value b)} -> Bool
consTest _ _ = True

-- Fails!
test1 : Bool
test1 = consTest (Wrap 3) (Wrap 4) -- {p = ?foo}

-- Succeeds!
test2 : Bool
test2 = consTest (Wrap 3) (Wrap 4) {p = Seq12}

-- Succeeds!
test3 : Bool
test3 = consTest (Wrap 3) (Wrap 4) {p = (| Seq12, Seq21 |)}

-- Fails!
-- test4 : Bool
-- test4 = consTest (Wrap 3) (Wrap 4) {p = (| Seq21, Seq12 |)}

