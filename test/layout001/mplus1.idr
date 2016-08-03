mplus : Maybe a -> Maybe a -> Maybe a
mplus a b = ?mplus_rhs

factor : Maybe Int
factor = ?term_rhs

symbol : String -> Maybe Int
symbol = ?symbol_rhs

term : Maybe Int
term = ?term_rhs

term                          =  do f <- factor
                                    do symbol "*"
                                       t <- term
                                       pure (f * t)
                                   `mplus` pure f
