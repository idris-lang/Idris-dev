m_add : Maybe (Either Bool Int) -> Maybe (Either Bool Int) ->
        Maybe (Either Bool Int)
m_add x y = do x' <- x -- Extract value from x
               y' <- y -- Extract value from y
               case x' of
                  Left _ => Nothing
                  Right _ => Nothing
