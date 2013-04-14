module Data.Set

import Data.Map

-- TODO: add intersection, union, difference

data Set k = SetWrapper (Data.Map.Map k ())

empty : Set k
empty = SetWrapper Data.Map.empty

insert : Ord k => k -> Set k -> Set k
insert k (SetWrapper m) = SetWrapper (Data.Map.insert k () m)

delete : Ord k => k -> Set k -> Set k
delete k (SetWrapper m) = SetWrapper (Data.Map.delete k m)

contains : Ord k => k -> Set k -> Bool
contains k (SetWrapper m) = isJust (Data.Map.lookup k m)

fromList : Ord k => List k -> Set k
fromList l = SetWrapper (Data.Map.fromList (map (\i => (i, ())) l))

toList : Ord k => Set k -> List k
toList (SetWrapper m) = map (\(i, _) => i) (Data.Map.toList m)
