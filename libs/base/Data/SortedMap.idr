module Data.SortedMap

-- TODO: write merge and split

data Tree : Nat -> Type -> Type -> Type where
  Leaf : k -> v -> Tree Z k v
  Branch2 : Tree n k v -> k -> Tree n k v -> Tree (S n) k v
  Branch3 : Tree n k v -> k -> Tree n k v -> k -> Tree n k v -> Tree (S n) k v

branch4 :
  Tree n k v -> k ->
  Tree n k v -> k ->
  Tree n k v -> k ->
  Tree n k v ->
  Tree (S (S n)) k v
branch4 a b c d e f g =
  Branch2 (Branch2 a b c) d (Branch2 e f g)

branch5 :
  Tree n k v -> k ->
  Tree n k v -> k ->
  Tree n k v -> k ->
  Tree n k v -> k ->
  Tree n k v ->
  Tree (S (S n)) k v
branch5 a b c d e f g h i =
  Branch2 (Branch2 a b c) d (Branch3 e f g h i)

branch6 :
  Tree n k v -> k ->
  Tree n k v -> k ->
  Tree n k v -> k ->
  Tree n k v -> k ->
  Tree n k v -> k ->
  Tree n k v ->
  Tree (S (S n)) k v
branch6 a b c d e f g h i j k =
  Branch3 (Branch2 a b c) d (Branch2 e f g) h (Branch2 i j k)

branch7 :
  Tree n k v -> k ->
  Tree n k v -> k ->
  Tree n k v -> k ->
  Tree n k v -> k ->
  Tree n k v -> k ->
  Tree n k v -> k ->
  Tree n k v ->
  Tree (S (S n)) k v
branch7 a b c d e f g h i j k l m =
  Branch3 (Branch3 a b c d e) f (Branch2 g h i) j (Branch2 k l m)

merge1 : Tree n k v -> k -> Tree (S n) k v -> k -> Tree (S n) k v -> Tree (S (S n)) k v
merge1 a b (Branch2 c d e) f (Branch2 g h i) = branch5 a b c d e f g h i
merge1 a b (Branch2 c d e) f (Branch3 g h i j k) = branch6 a b c d e f g h i j k
merge1 a b (Branch3 c d e f g) h (Branch2 i j k) = branch6 a b c d e f g h i j k
merge1 a b (Branch3 c d e f g) h (Branch3 i j k l m) = branch7 a b c d e f g h i j k l m

merge2 : Tree (S n) k v -> k -> Tree n k v -> k -> Tree (S n) k v -> Tree (S (S n)) k v
merge2 (Branch2 a b c) d e f (Branch2 g h i) = branch5 a b c d e f g h i
merge2 (Branch2 a b c) d e f (Branch3 g h i j k) = branch6 a b c d e f g h i j k
merge2 (Branch3 a b c d e) f g h (Branch2 i j k) = branch6 a b c d e f g h i j k
merge2 (Branch3 a b c d e) f g h (Branch3 i j k l m) = branch7 a b c d e f g h i j k l m

merge3 : Tree (S n) k v -> k -> Tree (S n) k v -> k -> Tree n k v -> Tree (S (S n)) k v
merge3 (Branch2 a b c) d (Branch2 e f g) h i = branch5 a b c d e f g h i
merge3 (Branch2 a b c) d (Branch3 e f g h i) j k = branch6 a b c d e f g h i j k
merge3 (Branch3 a b c d e) f (Branch2 g h i) j k = branch6 a b c d e f g h i j k
merge3 (Branch3 a b c d e) f (Branch3 g h i j k) l m = branch7 a b c d e f g h i j k l m

treeLookup : Ord k => k -> Tree n k v -> Maybe v
treeLookup k (Leaf k' v) =
  if k == k' then
    Just v
  else
    Nothing
treeLookup k (Branch2 t1 k' t2) =
  if k <= k' then
    treeLookup k t1
  else
    treeLookup k t2
treeLookup k (Branch3 t1 k1 t2 k2 t3) =
  if k <= k1 then
    treeLookup k t1
  else if k <= k2 then
    treeLookup k t2
  else
    treeLookup k t3

treeInsert' : Ord k => k -> v -> Tree n k v -> Either (Tree n k v) (Tree n k v, k, Tree n k v)
treeInsert' k v (Leaf k' v') =
  case compare k k' of
    LT => Right (Leaf k v, k, Leaf k' v')
    EQ => Left (Leaf k v)
    GT => Right (Leaf k' v', k', Leaf k v)
treeInsert' k v (Branch2 t1 k' t2) =
  if k <= k' then
    case treeInsert' k v t1 of
      Left t1' => Left (Branch2 t1' k' t2)
      Right (a, b, c) => Left (Branch3 a b c k' t2)
  else
    case treeInsert' k v t2 of
      Left t2' => Left (Branch2 t1 k' t2')
      Right (a, b, c) => Left (Branch3 t1 k' a b c)
treeInsert' k v (Branch3 t1 k1 t2 k2 t3) =
  if k <= k1 then
    case treeInsert' k v t1 of
      Left t1' => Left (Branch3 t1' k1 t2 k2 t3)
      Right (a, b, c) => Right (Branch2 a b c, k1, Branch2 t2 k2 t3)
  else
    if k <= k2 then
      case treeInsert' k v t2 of
        Left t2' => Left (Branch3 t1 k1 t2' k2 t3)
        Right (a, b, c) => Right (Branch2 t1 k1 a, b, Branch2 c k2 t3)
    else
      case treeInsert' k v t3 of
        Left t3' => Left (Branch3 t1 k1 t2 k2 t3')
        Right (a, b, c) => Right (Branch2 t1 k2 t2, k2, Branch2 a b c)

treeInsert : Ord k => k -> v -> Tree n k v -> Either (Tree n k v) (Tree (S n) k v)
treeInsert k v t =
  case treeInsert' k v t of
    Left t' => Left t'
    Right (a, b, c) => Right (Branch2 a b c)

delType : Nat -> Type -> Type -> Type
delType Z k v = ()
delType (S n) k v = Tree n k v

treeDelete : Ord k => k -> Tree n k v -> Either (Tree n k v) (delType n k v)
treeDelete k (Leaf k' v) =
  if k == k' then
    Right ()
  else
    Left (Leaf k' v)
treeDelete {n=S Z} k (Branch2 t1 k' t2) =
  if k <= k' then
    case treeDelete k t1 of
      Left t1' => Left (Branch2 t1' k' t2)
      Right () => Right t2
  else
    case treeDelete k t2 of
      Left t2' => Left (Branch2 t1 k' t2')
      Right () => Right t1
treeDelete {n=S Z} k (Branch3 t1 k1 t2 k2 t3) =
  if k <= k1 then
    case treeDelete k t1 of
      Left t1' => Left (Branch3 t1' k1 t2 k2 t3)
      Right () => Left (Branch2 t2 k2 t3)
  else if k <= k2 then
    case treeDelete k t2 of
      Left t2' => Left (Branch3 t1 k1 t2' k2 t3)
      Right () => Left (Branch2 t1 k1 t3)
  else
    case treeDelete k t3 of
      Left t3' => Left (Branch3 t1 k1 t2 k2 t3')
      Right () => Left (Branch2 t1 k1 t2)
treeDelete {n=S (S _)} k (Branch2 t1 k' t2) =
  if k <= k' then
    case treeDelete k t1 of
      Left t1' => Left (Branch2 t1' k' t2)
      Right t1' =>
        case t2 of
          Branch2 a b c => Right (Branch3 t1' k' a b c)
          Branch3 a b c d e => Left (branch4 t1' k' a b c d e)
  else
    case treeDelete k t2 of
      Left t2' => Left (Branch2 t1 k' t2')
      Right t2' =>
        case t1 of
          Branch2 a b c => Right (Branch3 a b c k' t2')
          Branch3 a b c d e => Left (branch4 a b c d e k' t2')
treeDelete {n=(S (S _))} k (Branch3 t1 k1 t2 k2 t3) =
  if k <= k1 then
    case treeDelete k t1 of
      Left t1' => Left (Branch3 t1' k1 t2 k2 t3)
      Right t1' => Left (merge1 t1' k1 t2 k2 t3)
  else if k <= k2 then
    case treeDelete k t2 of
      Left t2' => Left (Branch3 t1 k1 t2' k2 t3)
      Right t2' => Left (merge2 t1 k1 t2' k2 t3)
  else
    case treeDelete k t3 of
      Left t3' => Left (Branch3 t1 k1 t2 k2 t3')
      Right t3' => Left (merge3 t1 k1 t2 k2 t3')

treeToList : Ord k => Tree n k v -> List (k, v)
treeToList = treeToList' (:: [])
  where
    treeToList' : Ord k => ((k, v) -> List (k, v)) -> Tree n k v -> List (k, v)
    treeToList' cont (Leaf k v) = cont (k, v)
    treeToList' cont (Branch2 t1 _ t2) = treeToList' (:: treeToList' cont t2) t1
    treeToList' cont (Branch3 t1 _ t2 _ t3) = treeToList' (:: treeToList' (:: treeToList' cont t3) t2) t1

data SortedMap : Type -> Type -> Type where
  Empty : SortedMap k v
  M : (n:Nat) -> Tree n k v -> SortedMap k v

empty : SortedMap k v
empty = Empty

lookup : Ord k => k -> SortedMap k v -> Maybe v
lookup _ Empty = Nothing
lookup k (M _ t) = treeLookup k t

insert : Ord k => k -> v -> SortedMap k v -> SortedMap k v
insert k v Empty = M Z (Leaf k v)
insert k v (M _ t) =
  case treeInsert k v t of
    Left t' => (M _ t')
    Right t' => (M _ t')

delete : Ord k => k -> SortedMap k v -> SortedMap k v
delete _ Empty = Empty
delete k (M Z t) =
  case treeDelete k t of
    Left t' => (M _ t')
    Right () => Empty
delete k (M (S _) t) =
  case treeDelete k t of
    Left t' => (M _ t')
    Right t' => (M _ t')

fromList : Ord k => List (k, v) -> SortedMap k v
fromList l = foldl (flip (uncurry insert)) empty l

toList : Ord k => SortedMap k v -> List (k, v)
toList Empty = []
toList (M _ t) = treeToList t

instance Functor (Tree n k) where
  map f (Leaf k v) = Leaf k (f v)
  map f (Branch2 t1 k t2) = Branch2 (map f t1) k (map f t2)
  map f (Branch3 t1 k1 t2 k2 t3) = Branch3 (map f t1) k1 (map f t2) k2 (map f t3)

instance Functor (SortedMap k) where
  map _ Empty = Empty
  map f (M n t) = M _ (map f t)
