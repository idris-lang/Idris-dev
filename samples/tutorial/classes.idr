m_add : Maybe Int -> Maybe Int -> Maybe Int
m_add x y = do x' <- x -- Extract value from x
               y' <- y -- Extract value from y
               pure (x' + y') -- Add them

m_add' : Maybe Int -> Maybe Int -> Maybe Int
m_add' x y = [ x' + y' | x' <- x, y' <- y ]

sortAndShow : (Ord a, Show a) => List a -> String
sortAndShow xs = show (sort xs)
