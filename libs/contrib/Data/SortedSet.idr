module Data.SortedSet

import Data.SortedMap

-- TODO: add intersection, union, difference

abstract
data SortedSet k = SetWrapper (Data.SortedMap.SortedMap k ())

public
empty : Ord k => SortedSet k
empty = SetWrapper Data.SortedMap.empty

public
insert : k -> SortedSet k -> SortedSet k
insert k (SetWrapper m) = SetWrapper (Data.SortedMap.insert k () m)

public
delete : k -> SortedSet k -> SortedSet k
delete k (SetWrapper m) = SetWrapper (Data.SortedMap.delete k m)

public
contains : k -> SortedSet k -> Bool
contains k (SetWrapper m) = isJust (Data.SortedMap.lookup k m)

public
fromList : Ord k => List k -> SortedSet k
fromList l = SetWrapper (Data.SortedMap.fromList (map (\i => (i, ())) l))

public
toList : SortedSet k -> List k
toList (SetWrapper m) = map (\(i, _) => i) (Data.SortedMap.toList m)

instance Foldable SortedSet where
  foldr f e xs = foldr f e (Data.SortedSet.toList xs)
