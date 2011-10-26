
data Maybe a = Nothing | Just a;

maybe : b -> (a -> b) -> Maybe a -> b;
maybe n j Nothing  = n;
maybe n j (Just x) = j x;

