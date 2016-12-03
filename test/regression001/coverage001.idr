module Data.AVL.Tree

%default total
%access export

data Balance : Nat -> Nat -> Type where
  LHeavy   : Balance (S n) n
  RHeavy   : Balance n     (S n)
  Balanced : Balance n     n

%name Balance b, bal
    
height : Balance n m -> Nat
height b = S (height' b)
  where
    height' : Balance n m -> Nat
    height' (LHeavy {n}) = S n
    height' (RHeavy {n}) = S n
    height' {n} (Balanced {n}) = n

public export
data Tree : (keyTy : Type) -> (valTy : Type) -> Type
  where
    ||| An empty Tree node.
    Empty : Tree k v

    Node : (key   : k)
        -> (val   : v)
        -> (left  : Tree k v)
        -> (right : Tree k v)
        -> Tree k v

%name Tree t, tree

public export
data AVLInvariant : (height : Nat)
                 -> (tree   : Tree k v)
                 -> Type
  where
    AVLEmpty : AVLInvariant 0 Empty

    AVLNode : (left  : AVLInvariant n l) -> 
              (right :  AVLInvariant m r) -> 
              (b : Balance n m) -> 
              AVLInvariant (height b) (Node k v l r)

%name AVLInvariant inv

public export
AVLTree : (height : Nat) -> (keyTy : Type) -> (valueTy : Type) -> Type
AVLTree n k v = Subset (Tree k v) (AVLInvariant n)

-- --------------------------------------------------------------- [ Rotations ]
private
data InsertRes : Nat -> (k : Type) -> Type -> Type where
  Same : AVLTree n k v     -> InsertRes n k v
  Grew : AVLTree (S n) k v -> InsertRes n k v

%name InsertRes res, r

private
runInsertRes : InsertRes n k v -> (n : Nat ** AVLTree n k v)
runInsertRes (Same t) = (_ ** t)
runInsertRes (Grew t) = (_ ** t)

||| Perform a Left roation.
private
rotLeft : k
       -> v
       -> AVLTree n k v
       -> AVLTree (S (S n)) k v
       -> InsertRes (S (S n)) k v
-- Impossible because Empty has depth 0 and we know the depth is at least 2 from the type
rotLeft key val l (Element Empty AVLEmpty) impossible
rotLeft key val (Element l invl) (Element (Node key' val' rl rr) (AVLNode invrl invrr Balanced)) = ?rl1
rotLeft key val (Element l invl) (Element (Node key' val' (Node key'' val'' rll rlr) rr) (AVLNode (AVLNode invrll invrlr LHeavy) invrr LHeavy)) = ?rl2
rotLeft key val (Element l invl) (Element (Node key' val' (Node key'' val'' rll rlr) rr) (AVLNode (AVLNode invrll invrlr RHeavy) invrr LHeavy)) = ?rl3
rotLeft key val (Element l invl) (Element (Node key' val' (Node key'' val'' rll rlr) rr) (AVLNode (AVLNode invrll invrlr Balanced) invrr LHeavy)) = ?rl4
rotLeft key val (Element l invl) (Element (Node key' val' rl rr) (AVLNode invrl invrr RHeavy)) = ?rl5
