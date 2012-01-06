module prelude.maybe

data Maybe a = Nothing | Just a

maybe : |(def : b) -> (a -> b) -> Maybe a -> b
maybe n j Nothing  = n
maybe n j (Just x) = j x

maybe_bind : Maybe a -> (a -> Maybe b) -> Maybe b
maybe_bind Nothing k = Nothing
maybe_bind (Just x) k = k x

