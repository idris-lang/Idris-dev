module Data.SortedSet

import Data.SortedMap

-- TODO: add intersection, union, difference

data SortedSet k = SetWrapper (Data.SortedMap.SortedMap k ())

empty : SortedSet k
empty = SetWrapper Data.SortedMap.empty

insert : Ord k => k -> SortedSet k -> SortedSet k
insert k (SetWrapper m) = SetWrapper (Data.SortedMap.insert k () m)

delete : Ord k => k -> SortedSet k -> SortedSet k
delete k (SetWrapper m) = SetWrapper (Data.SortedMap.delete k m)

contains : Ord k => k -> SortedSet k -> Bool
contains k (SetWrapper m) = isJust (Data.SortedMap.lookup k m)

fromList : Ord k => List k -> SortedSet k
fromList l = SetWrapper (Data.SortedMap.fromList (map (\i => (i, ())) l))

toList : SortedSet k -> List k
toList (SetWrapper m) = map (\(i, _) => i) (Data.SortedMap.toList m)

implementation Foldable SortedSet where
  foldr f e xs = foldr f e (Data.SortedSet.toList xs)
