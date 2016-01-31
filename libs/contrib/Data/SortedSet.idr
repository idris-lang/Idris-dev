module Data.SortedSet

import Data.SortedMap

-- TODO: add intersection, union, difference

export
data SortedSet k = SetWrapper (Data.SortedMap.SortedMap k ())

export
empty : Ord k => SortedSet k
empty = SetWrapper Data.SortedMap.empty

export
insert : k -> SortedSet k -> SortedSet k
insert k (SetWrapper m) = SetWrapper (Data.SortedMap.insert k () m)

export
delete : k -> SortedSet k -> SortedSet k
delete k (SetWrapper m) = SetWrapper (Data.SortedMap.delete k m)

export
contains : k -> SortedSet k -> Bool
contains k (SetWrapper m) = isJust (Data.SortedMap.lookup k m)

export
fromList : Ord k => List k -> SortedSet k
fromList l = SetWrapper (Data.SortedMap.fromList (map (\i => (i, ())) l))

export
toList : SortedSet k -> List k
toList (SetWrapper m) = map (\(i, _) => i) (Data.SortedMap.toList m)

implementation Foldable SortedSet where
  foldr f e xs = foldr f e (Data.SortedSet.toList xs)
