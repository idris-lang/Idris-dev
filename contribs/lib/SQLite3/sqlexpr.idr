module main
import prelude.list

-----------------------------------------------------------
-- * SQL data type
-----------------------------------------------------------
        
data Value = VInt Int
            |VStr String
            |VCol String

data Cond = Equals Value Value
            |MkGT Value Value
            |MkGTE Value Value
            |MkLT Value Value
            |MkLTE Value Value
--TODO            |MkIN (List Value)
--TODO            |MkIN SQL

              
data Clause = MkCond Cond
             | AND Clause Clause
             | OR Clause Clause
             | Empty
             
data SelVar = Cols (List String)
              |ALL

data SQL  = SELECT SelVar SQL Clause
            | TBL String 
            | INSERT SQL (List Value)
            

foldr1 : (a -> a -> a) -> List a -> a	
foldr1 f [x] = x
foldr1 f (x::xs) = f x (foldr1 f xs)


unwords' : List (List Char) -> List Char
unwords' [] = []                         
unwords' ws = (foldr1 addSpace ws)
        where
            addSpace : List Char -> List Char -> List Char
            addSpace w s = w ++ (' ' :: s) 
          
               
unwords :  List String -> String
unwords = pack . unwords' . map unpack


mapping : Int -> List a -> List (Int, a)
mapping counter [] = []
mapping counter (x :: xs) = (counter, x) :: mapping (counter + 1) xs


popintoList : Maybe Value -> List (Maybe Value) -> List (Maybe Value)
popintoList (Just x) [] =  [(Just x)]
popintoList (Just (x)) ((Just x) :: xs) =  (popintoList (Just x) xs)
popintoList Nothing [] = []

valString : List (Maybe Value) -> Value -> (String, List (Maybe Value))
valString xs (VInt x) = ("?", xs ++ [Just (VInt x)])
valString xs (VStr x) = ("?", xs ++ [Just (VStr x)])
valString xs (VCol n) = (n, xs)   


evalCond : List (Maybe Value) -> Cond -> (String, List (Maybe Value))
evalCond xs (Equals val1 val2) = let (restring , newxs ) = valString xs val1 in
                                 let (restring2, newxs') = valString newxs val2 in
                                     (restring ++ " = " ++ restring2, (newxs ++ newxs'))
                                     
evalCond xs (MkGT val1 val2) = let (restring , newxs ) = valString xs val1 in
                                 let (restring2, newxs') = valString newxs val2 in
                                     (restring ++ " > " ++ restring2, (newxs ++ newxs'))

evalCond xs (MkGTE val1 val2) = let (restring , newxs ) = valString xs val1 in
                                 let (restring2, newxs') = valString newxs val2 in
                                     (restring ++ " >= " ++ restring2, (newxs ++ newxs'))

evalCond xs (MkLT val1 val2) = let (restring , newxs ) = valString xs val1 in
                                 let (restring2, newxs') = valString newxs val2 in
                                     (restring ++ " < " ++ restring2, (newxs ++ newxs'))
                                     
evalCond xs (MkLTE val1 val2) = let (restring , newxs ) = valString xs val1 in
                                 let (restring2, newxs') = valString newxs val2 in
                                     (restring ++ " =< " ++ restring2, (newxs ++ newxs'))
                                                                                                                                                    
                                     
clauseString : List (Maybe Value) -> Clause -> (String, List (Maybe Value))
clauseString xs (Empty) = ("" , []) -- No condition
clauseString xs (MkCond cond') = let (condstr, newxs) = evalCond xs cond' in
                                     (condstr , newxs)

clauseString xs (AND c1 c2) = let (clausestr, newxs) = clauseString xs c1 in
                              let (clausestr2, newxs') = clauseString newxs c2 in
                                  (clausestr ++ " AND " ++clausestr2 , newxs')
                                  
clauseString xs (OR c1 c2) =  let (clausestr, newxs) = clauseString xs c1 in
                              let (clausestr2, newxs') = clauseString newxs c2 in
                                  (clausestr ++ " OR " ++clausestr2 , newxs')
                                  
                                                               
varString : List String -> String
varString xs = (unwords xs)
                       
                              
evalSQL : List (Maybe Value) -> SQL -> ( String, List (Maybe Value))
evalSQL xs (TBL tbl) = (tbl, xs)
evalSQL xs (SELECT vars sql' c) = let (sqlstring, newxs) = evalSQL xs sql' in
                                  let (csstring, newxs') = clauseString newxs c in
                                  case c of 
                                        Empty => case vars of 
                                                      (ALL ) => ("SELECT " ++ "*" ++ " FROM (" ++ sqlstring ++ ") " ++ csstring, map snd ( mapping 0 newxs'))
                                                      (Cols selvar) => ("SELECT " ++ unwords ( intersperse "" ( selvar ++ (words ( " FROM (" ++ sqlstring ++ ")")))) ++ csstring, map snd ( mapping 0 newxs'))
                                                      
                                        _  => case vars of 
                                                   (ALL ) => ("SELECT " ++ "*" ++ " FROM (" ++ sqlstring ++ ") " ++ "WHERE" ++ csstring, map snd ( mapping 0 newxs'))
                                                   (Cols selvar) => ("SELECT " ++ unwords ( intersperse "" ( selvar ++ (words ( " FROM (" ++ sqlstring ++ ")")))) ++ "WHERE" ++ csstring, map snd ( mapping 0 newxs'))


display : (String, List (Maybe Value)) -> String
display (x, (xs)) = show x 
                 
evalSQL2 : List (Maybe Value) -> String -> (String, List (Maybe Value))
evalSQL2 [] sql = (sql, [])
evalSQL2 ((Just (VInt x)) :: xs) sql = let ("string" , newxs) = evalSQL2 xs sql in
                                        ("string" ++ sql , Just (VInt x) :: newxs)

main : IO ()
main = print (display(evalSQL [] ((SELECT ALL)(TBL "tbl") (MkCond (Equals (VCol "col")(VInt 1))))))

                            