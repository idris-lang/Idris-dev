module RBTree
 
data Colour = Red | Black

data RBTree : Type -> Type -> Nat -> Colour -> Type where
  Leaf : RBTree k v O Black
  RedBranch : k -> v -> RBTree k v n Black -> RBTree k v n Black -> RBTree k v n Red
  BlackBranch : k -> v -> RBTree k v n x -> RBTree k v n y -> RBTree k v (S n) Black
 
toBlack : RBTree k v n c -> (m ** (RBTree k v m Black, Either (m = n) (m = (S n))))
toBlack (RedBranch k v l r) = (_ ** (BlackBranch k v l r, Right refl))
toBlack Leaf = (_ ** (Leaf, Left refl))
toBlack (BlackBranch k v l r) = (_ ** (BlackBranch k v l r, Left refl))
 
total
lookup : Ord k => k -> RBTree k v n Black -> Maybe v
lookup k Leaf = Nothing
lookup k (BlackBranch k0 v0 l r) =
  case compare k k0 of
    EQ => Just v0
    LT =>
      let (_ ** (t, _)) = toBlack l in
            lookup k t
    GT =>
      let (_ ** (t, _)) = toBlack r in
            lookup k t 

