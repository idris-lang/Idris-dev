module Data.SortedMap

-- TODO: write merge and split

private
data Tree : Nat -> (k : Type) -> Type -> Ord k -> Type where
  Leaf : k -> v -> Tree Z k v o
  Branch2 : Tree n k v o -> k -> Tree n k v o -> Tree (S n) k v o
  Branch3 : Tree n k v o -> k -> Tree n k v o -> k -> Tree n k v o -> Tree (S n) k v o

branch4 :
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o ->
  Tree (S (S n)) k v o
branch4 a b c d e f g =
  Branch2 (Branch2 a b c) d (Branch2 e f g)

branch5 :
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o ->
  Tree (S (S n)) k v o
branch5 a b c d e f g h i =
  Branch2 (Branch2 a b c) d (Branch3 e f g h i)

branch6 :
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o ->
  Tree (S (S n)) k v o
branch6 a b c d e f g h i j k =
  Branch3 (Branch2 a b c) d (Branch2 e f g) h (Branch2 i j k)

branch7 :
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o ->
  Tree (S (S n)) k v o
branch7 a b c d e f g h i j k l m =
  Branch3 (Branch3 a b c d e) f (Branch2 g h i) j (Branch2 k l m)

merge1 : Tree n k v o -> k -> Tree (S n) k v o -> k -> Tree (S n) k v o -> Tree (S (S n)) k v o
merge1 a b (Branch2 c d e) f (Branch2 g h i) = branch5 a b c d e f g h i
merge1 a b (Branch2 c d e) f (Branch3 g h i j k) = branch6 a b c d e f g h i j k
merge1 a b (Branch3 c d e f g) h (Branch2 i j k) = branch6 a b c d e f g h i j k
merge1 a b (Branch3 c d e f g) h (Branch3 i j k l m) = branch7 a b c d e f g h i j k l m

merge2 : Tree (S n) k v o -> k -> Tree n k v o -> k -> Tree (S n) k v o -> Tree (S (S n)) k v o
merge2 (Branch2 a b c) d e f (Branch2 g h i) = branch5 a b c d e f g h i
merge2 (Branch2 a b c) d e f (Branch3 g h i j k) = branch6 a b c d e f g h i j k
merge2 (Branch3 a b c d e) f g h (Branch2 i j k) = branch6 a b c d e f g h i j k
merge2 (Branch3 a b c d e) f g h (Branch3 i j k l m) = branch7 a b c d e f g h i j k l m

merge3 : Tree (S n) k v o -> k -> Tree (S n) k v o -> k -> Tree n k v o -> Tree (S (S n)) k v o
merge3 (Branch2 a b c) d (Branch2 e f g) h i = branch5 a b c d e f g h i
merge3 (Branch2 a b c) d (Branch3 e f g h i) j k = branch6 a b c d e f g h i j k
merge3 (Branch3 a b c d e) f (Branch2 g h i) j k = branch6 a b c d e f g h i j k
merge3 (Branch3 a b c d e) f (Branch3 g h i j k) l m = branch7 a b c d e f g h i j k l m

treeLookup : k -> Tree n k v o -> Maybe v
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

treeInsert' : k -> v -> Tree n k v o -> Either (Tree n k v o) (Tree n k v o, k, Tree n k v o)
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
        Right (a, b, c) => Right (Branch2 t1 k1 t2, k2, Branch2 a b c)

treeInsert : k -> v -> Tree n k v o -> Either (Tree n k v o) (Tree (S n) k v o)
treeInsert k v t =
  case treeInsert' k v t of
    Left t' => Left t'
    Right (a, b, c) => Right (Branch2 a b c)

delType : Nat -> (k : Type) -> Type -> Ord k -> Type
delType Z k v o = ()
delType (S n) k v o = Tree n k v o

treeDelete : k -> Tree n k v o -> Either (Tree n k v o) (delType n k v o)
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

treeToList : Tree n k v o -> List (k, v)
treeToList = treeToList' (:: [])
  where
    treeToList' : ((k, v) -> List (k, v)) -> Tree n k v o -> List (k, v)
    treeToList' cont (Leaf k v) = cont (k, v)
    treeToList' cont (Branch2 t1 _ t2) = treeToList' (:: treeToList' cont t2) t1
    treeToList' cont (Branch3 t1 _ t2 _ t3) = treeToList' (:: treeToList' (:: treeToList' cont t3) t2) t1

export
data SortedMap : Type -> Type -> Type where
  Empty : Ord k => SortedMap k v
  M : (o : Ord k) => (n:Nat) -> Tree n k v o -> SortedMap k v

export
empty : Ord k => SortedMap k v
empty = Empty

export
lookup : k -> SortedMap k v -> Maybe v
lookup _ Empty = Nothing
lookup k (M _ t) = treeLookup k t

export
insert : k -> v -> SortedMap k v -> SortedMap k v
insert k v Empty = M Z (Leaf k v)
insert k v (M _ t) =
  case treeInsert k v t of
    Left t' => (M _ t')
    Right t' => (M _ t')

export
delete : k -> SortedMap k v -> SortedMap k v
delete _ Empty = Empty
delete k (M Z t) =
  case treeDelete k t of
    Left t' => (M _ t')
    Right () => Empty
delete k (M (S _) t) =
  case treeDelete k t of
    Left t' => (M _ t')
    Right t' => (M _ t')

export
fromList : Ord k => List (k, v) -> SortedMap k v
fromList l = foldl (flip (uncurry insert)) empty l

export
toList : SortedMap k v -> List (k, v)
toList Empty = []
toList (M _ t) = treeToList t

treeMap : (a -> b) -> Tree n k a o -> Tree n k b o
treeMap f (Leaf k v) = Leaf k (f v)
treeMap f (Branch2 t1 k t2) = Branch2 (treeMap f t1) k (treeMap f t2)
treeMap f (Branch3 t1 k1 t2 k2 t3) 
    = Branch3 (treeMap f t1) k1 (treeMap f t2) k2 (treeMap f t3)

implementation Functor (SortedMap k) where
  map _ Empty = Empty
  map f (M n t) = M _ (treeMap f t)

