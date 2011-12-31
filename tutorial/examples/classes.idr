m_add : Maybe Int -> Maybe Int -> Maybe Int;
m_add x y = do { x' <- x; -- Extract value from x
                 y' <- y; -- Extract value from y
                 return (x' + y'); -- Add them 
               };
