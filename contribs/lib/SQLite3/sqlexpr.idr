module main
import prelude.list

-----------------------------------------------------------
-- * SQL data type
-----------------------------------------------------------
        
data Value = VInt Int
            |VStr String
            |VFloat Float
            |VCol String
            |VNULL
            

data Cond = Equals Value Value
            |MkGT Value Value
            |MkGTE Value Value
            |MkLT Value Value
            |MkLTE Value Value
            |MkNULL Value

              
data Clause = MkCond Cond
             | AND Clause Clause
             | OR Clause Clause
             | Empty

data condClause = SET Clause
                  |WHERE condClause Clause
             
data SelVar = Cols (List String)
              |ALL

data SQL  = SELECT SelVar SQL Clause
            | TBL String 
            | INSERT SQL (List Value)
            | INSERTC SQL (List Value) (List Value)
            | UPDATE SQL condClause
            | CREATE SQL (List Value)
            
-- remember to remove these funcs later
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

valString : List (Maybe(Int, Value)) -> Value -> (String, List (Maybe(Int, Value)))
valString xs (VInt x) = ("?" ++ show (cast(length xs)+1), xs ++ [Just (cast((length xs)+1),(VInt x))])
valString xs (VStr x) = ("?" ++ show (cast(length xs)+1), xs ++ [Just (cast((length xs)+1),(VStr x))])
valString xs (VFloat x) = ("?" ++ show (cast(length xs)+1), xs ++ [Just (cast((length xs)+1),(VFloat x))])
valString xs (VCol n) = (n, xs)  

listVal : List (Maybe(Int, Value)) -> List Value -> (String, List (Maybe(Int, Value)))
listVal xs [] = ("", xs)
listVal xs (v::vs) = let (str, newxs) = (valString xs v) in
                      let (str', newxs') = listVal newxs vs in
                          ((unwords(intersperse  "," (words(str) ++ words (str')))), newxs')

evalCond : List (Maybe(Int, Value)) -> Cond -> (String, List (Maybe(Int, Value)))
evalCond xs (Equals val1 val2) = let (restring , newxs ) = valString xs val1 in
                                 let (restring2, newxs') = valString newxs val2 in
                                     (restring ++ " = " ++ restring2, (newxs'))
                                     
evalCond xs (MkGT val1 val2) = let (restring , newxs ) = valString xs val1 in
                                 let (restring2, newxs') = valString newxs val2 in
                                     (restring ++ " > " ++ restring2, (newxs'))

evalCond xs (MkGTE val1 val2) = let (restring , newxs ) = valString xs val1 in
                                 let (restring2, newxs') = valString newxs val2 in
                                     (restring ++ " >= " ++ restring2, ( newxs'))

evalCond xs (MkLT val1 val2) = let (restring , newxs ) = valString xs val1 in
                                 let (restring2, newxs') = valString newxs val2 in
                                     (restring ++ " < " ++ restring2, (newxs'))
                                     
evalCond xs (MkLTE val1 val2) = let (restring , newxs ) = valString xs val1 in
                                 let (restring2, newxs') = valString newxs val2 in
                                     (restring ++ " =< " ++ restring2, ( newxs'))
                                                                                                                                                    
evalCond xs (MkNULL val) = let (restring , newxs ) = valString xs val in
                               (restring ++ " IS NULL " , newxs)
                                     
clauseString : List (Maybe(Int, Value)) -> Clause -> (String, List (Maybe(Int, Value)))
clauseString xs (Empty) = ("" , []) -- No condition
clauseString xs (MkCond cond') = let (condstr, newxs) = evalCond xs cond' in
                                     (condstr , newxs)

clauseString xs (AND c1 c2) = let (clausestr, newxs) = clauseString xs c1 in
                              let (clausestr2, newxs') = clauseString newxs c2 in
                                  (clausestr ++ " AND " ++clausestr2 , newxs')
                                  
clauseString xs (OR c1 c2) =  let (clausestr, newxs) = clauseString xs c1 in
                              let (clausestr2, newxs') = clauseString newxs c2 in
                                  (clausestr ++ " OR " ++clausestr2 , newxs')
                                                        
condClauseStr : List (Maybe(Int, Value)) -> condClause -> (String, List (Maybe(Int, Value)))
condClauseStr xs (SET setcl) = let (condstr, newxs) = clauseString xs setcl in
                                   (" SET " ++ condstr, newxs)
                                   
condClauseStr xs (WHERE setcl1 setcl2) = let (condstr, newxs) = condClauseStr xs setcl1 in
                                         let (condstr', newxs') = clauseString newxs setcl2 in
                                             ( condstr ++ " WHERE " ++ condstr', newxs')

                              
evalSQL : List (Maybe(Int, Value)) -> SQL -> ( String, List (Maybe(Int, Value)))
evalSQL xs (TBL tbl) = (tbl, xs)
evalSQL xs (SELECT vars sql' c) = let (sqlstring, newxs) = evalSQL xs sql' in
                                  let (csstring, newxs') = clauseString newxs c in
                                  case c of 
                                        Empty => case vars of 
                                                      (ALL ) => ("SELECT " ++ "*" ++ " FROM (" 
                                                                ++ sqlstring ++ ") " ++ csstring++ ";",  newxs')
                                                      (Cols selvar) => ("SELECT " ++ unwords ( intersperse "" ( selvar ++ 
                                                                       (words ( " FROM (" ++ sqlstring ++ ")")))) ++ csstring++ ";",  newxs')
                                                      
                                        _  => case vars of 
                                                   (ALL ) => ("SELECT " ++ "*" ++ " FROM (" 
                                                             ++ sqlstring ++ ") " ++ "WHERE " ++ csstring++ ";",  newxs')
                                                   (Cols selvar) => ("SELECT " ++ unwords ( intersperse "" ( selvar ++
                                                                    (words ( " FROM (" ++ sqlstring ++ ")")))) ++ "WHERE" ++ csstring ++ ";", newxs')

evalSQL xs (INSERT sql vals) = let (tblname, newvals) = evalSQL xs sql in 
                               let (str, newxs ) = listVal newvals vals in  
                                   ("INSERT INTO " ++ tblname ++ " VALUES (" ++ str ++ ")"  , newxs)

evalSQL xs (INSERTC sql cols vals) = let (tblname, newvals) = evalSQL xs sql in 
                                     let (strcol, newcol) = listVal newvals cols in
                                     let (strval, newcolval) = listVal newcol vals in
                                         ("INSERT INTO " ++ tblname ++ "(" ++ strcol ++ ")" ++ "VALUES (" ++  strval ++ ")", newcolval)


evalSQL xs (UPDATE sql cl) = let (tblname, newxs) = evalSQL xs sql in
                               let (csstring, newxs') = condClauseStr newxs cl in
                                   ("UPDATE " ++ tblname ++ csstring, newxs')

                            