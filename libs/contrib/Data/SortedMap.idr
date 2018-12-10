module Data.SortedMap

-- TODO: write split

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
insertFrom : Foldable f => f (k, v) -> SortedMap k v -> SortedMap k v
insertFrom = flip $ foldl $ flip $ uncurry insert

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

||| Gets the keys of the map.
export
keys : SortedMap k v -> List k
keys = map fst . toList

||| Gets the values of the map. Could contain duplicates.
export
values : SortedMap k v -> List v
values = map snd . toList

export
null : SortedMap k v -> Bool
null Empty = True
null (M _ _) = False

treeMap : (a -> b) -> Tree n k a o -> Tree n k b o
treeMap f (Leaf k v) = Leaf k (f v)
treeMap f (Branch2 t1 k t2) = Branch2 (treeMap f t1) k (treeMap f t2)
treeMap f (Branch3 t1 k1 t2 k2 t3)
    = Branch3 (treeMap f t1) k1 (treeMap f t2) k2 (treeMap f t3)

export
implementation Functor (SortedMap k) where
  map _ Empty = Empty
  map f (M n t) = M _ (treeMap f t)

||| Merge two maps. When encountering duplicate keys, using a function to combine the values.
||| Uses the ordering of the first map given.
export
mergeWith : (v -> v -> v) -> SortedMap k v -> SortedMap k v -> SortedMap k v
mergeWith f x y = insertFrom inserted x where
  inserted : List (k, v)
  inserted = do
    (k, v) <- toList y
    let v' = (maybe id f $ lookup k x) v
    pure (k, v')

||| Merge two maps using the Semigroup (and by extension, Monoid) operation.
||| Uses mergeWith internally, so the ordering of the left map is kept.
export
merge : Semigroup v => SortedMap k v -> SortedMap k v -> SortedMap k v
merge = mergeWith (<+>)

||| Left-biased merge, also keeps the ordering specified  by the left map.
export
mergeLeft : SortedMap k v -> SortedMap k v -> SortedMap k v
mergeLeft = mergeWith const

export
(Show k, Show v) => Show (SortedMap k v) where
   show m = "fromList " ++ (show $ toList m)

-- TODO: is this the right variant of merge to use for this? I think it is, but
-- I could also see the advantages of using `mergeLeft`. The current approach is
-- strictly more powerful I believe, because `mergeLeft` can be emulated with
-- the `First` monoid. However, this does require more code to do the same
-- thing.
export
Semigroup v => Semigroup (SortedMap k v) where
  (<+>) = merge

||| For `neutral <+> y`, y is rebuilt in `Ord k`, so this is not a "strict" Monoid.
||| However, semantically, it should be equal.
export
(Ord k, Semigroup v) => Monoid (SortedMap k v) where
  neutral = empty
