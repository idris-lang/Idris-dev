module Sqlexpr
import Prelude.List

-----------------------------------------------------------------------------
-- |
-- Module      :  sqlexpr
-- Copyright   :  (c) The University of St Andrews, 2012
--
-- Implementations for SQLite query data type.
--
-----------------------------------------------------------------------------


-----------------------------------------------------------
-- | SQL data type
-----------------------------------------------------------

data Value = VInt Int
           | VStr String
           | VFloat Float
           | VCol String
           | VNULL

--Perhaps could extend this by adding
-- a dot operator to allow mapping
-- between table and column and
-- comparing different table columns.

data Cond = Equals Value Value
          | MkGT Value Value
          | MkGTE Value Value
          | MkLT Value Value
          | MkLTE Value Value
          | MkNULL Value

data SelVar = Cols (List String)
            | ALL

data ColType = CInt String -- parsed as string "int"
             | Varchar String



mutual
  data Clause = MkCond Cond
              | AND Clause Clause
              | OR Clause Clause
              | Empty
              | MkSQL SQL

  data condClause = SET Clause
                  | WHERE condClause Clause

  data Constr = NOTNULL
              | UNIQUE Constr
              | None
              | PRIMARYKEY
              | FOREIGNKEY
              | CHECK
              | DEFAULT


  data SQL  = SELECT SelVar SQL Clause
            | TBL (List String)
            | INSERT SQL (List Value)
            | INSERTC SQL (List Value) (List Value)
            | UPDATE SQL condClause
            | CREATE SQL (List (Value, ColType , Constr))

-- remember to remove these funcs later
-- foldr1 : (a -> a -> a) -> List a -> a
-- foldr1 f [x] = x
-- foldr1 f (x::xs) = f x (foldr1 f xs)


-- unwords' : List (List Char) -> List Char
-- unwords' [] = []
-- unwords' ws = (foldr1 addSpace ws)
--         where
--             addSpace : List Char -> List Char -> List Char
--             addSpace w s = w ++ (' ' :: s)
--
--
-- unwords :  List String -> String
-- unwords = pack . unwords' . map unpack

-----------------------------------------------------------
-- | This function replaces values with question mark
-- following by an index number. It then puts the value
-- replaced, in the list.
-----------------------------------------------------------

valString : List (Maybe (Int, Value)) -> Value -> (String, List (Maybe (Int, Value)))
valString xs (VInt x)   = ("?" ++ show (cast (length xs) + 1), xs ++ [Just (cast ((length xs) + 1), (VInt x))])
valString xs (VStr x)   = ("?" ++ show (cast (length xs) + 1), xs ++ [Just (cast ((length xs) + 1), (VStr x))])
valString xs (VFloat x) = ("?" ++ show (cast (length xs) + 1), xs ++ [Just (cast ((length xs) + 1), (VFloat x))])
valString xs (VCol n)   = (n, xs)

-----------------------------------------------------------
-- | This function calls valString on a list of Values
-- and separates the values by commas.
-----------------------------------------------------------

listVal : List (Maybe (Int, Value)) -> List Value -> (String, List (Maybe (Int, Value)))
listVal xs []      = ("", xs)
listVal xs (v::vs) = let (str, newxs) = (valString xs v) in
                     let (str', newxs') = listVal newxs vs in
                       (unwords (intersperse  "," (words (str) ++ words (str'))), newxs')

-----------------------------------------------------------
-- | Parses the type of column to be created.
-----------------------------------------------------------

getColType : List (Maybe (Int, Value)) -> ColType -> (String, List (Maybe (Int, Value)))
getColType xs (CInt x) = ("int", xs)
getColType xs (Varchar str) = ("varchar(255)", xs)

-----------------------------------------------------------
-- | CREATE Constraints
-----------------------------------------------------------

getConstr : List (Maybe (Int, Value)) -> Constr -> (String, List (Maybe (Int, Value)))
getConstr xs (NOTNULL)       = ("NOT NULL", xs)
getConstr xs (UNIQUE constr) = ("NOT NULL UNIQUE", xs)
getConstr xs (PRIMARYKEY)    = ("PRIMARY KEY", xs)
getConstr xs (FOREIGNKEY)    = ("FOREIGN KEY", xs)
getConstr xs (CHECK)         = ("CHECK", xs)
getConstr xs (DEFAULT)       = ("DEFAULT", xs)
getConstr xs (None)          = ("", xs)

putBrackets : String -> String
putBrackets str = "(" ++ str ++ ")"

-----------------------------------------------------------
-- | Used to detect a complex type in a nested SQLite query
-- This function is used for bracketing the nested queries.
-----------------------------------------------------------
complexType : SQL -> Bool
complexType (TBL tbl)           = False
complexType (SELECT vars sql c) = True

-----------------------------------------------------------
-- | Used in CREATE
-----------------------------------------------------------

listValType : List (Maybe (Int, Value)) -> List (Value, ColType , Constr) -> (String, List (Maybe (Int, Value)))
listValType xs [] = ("", xs)
listValType xs ((val, types, constr) :: vs) =
    let (str , newxs) = valString xs val in
    let (str' , newxs') = getColType newxs types in
    let (str'', newxs'') = getConstr newxs' constr in
    let (finalstr, finalxs) = listValType newxs'' vs in
    (unwords (intersperse  " " (words str ++ words str' ++ words str'' ++ words finalstr)) , finalxs)


-----------------------------------------------------------
-- | Evaluates a conditional WHERE clause
-----------------------------------------------------------

evalCond : List (Maybe (Int, Value)) -> Cond -> (String, List (Maybe (Int, Value)))
evalCond xs (Equals val1 val2) = let (restring , newxs ) = valString xs val1 in
                                 let (restring2, newxs') = valString newxs val2 in
                                 (restring ++ " = " ++ restring2, newxs')

evalCond xs (MkGT val1 val2) = let (restring , newxs ) = valString xs val1 in
                               let (restring2, newxs') = valString newxs val2 in
                               (restring ++ " > " ++ restring2, newxs')

evalCond xs (MkGTE val1 val2) = let (restring , newxs ) = valString xs val1 in
                                let (restring2, newxs') = valString newxs val2 in
                                (restring ++ " >= " ++ restring2, newxs')

evalCond xs (MkLT val1 val2) = let (restring , newxs ) = valString xs val1 in
                               let (restring2, newxs') = valString newxs val2 in
                               (restring ++ " < " ++ restring2, newxs')

evalCond xs (MkLTE val1 val2) = let (restring , newxs ) = valString xs val1 in
                                let (restring2, newxs') = valString newxs val2 in
                                (restring ++ " =< " ++ restring2, newxs')

evalCond xs (MkNULL val) = let (restring , newxs ) = valString xs val in
                           (restring ++ " IS NULL " , newxs)


-----------------------------------------------------------
-- | Evaluates clauses
-- Supports WHERE Clause
-- WHERE Clause And Another-Clause
-- WHERE Clause Or Another-Clause
-----------------------------------------------------------
clauseString : List (Maybe (Int, Value)) -> Clause -> (String, List (Maybe (Int, Value)))

clauseString xs (Empty) = ("" , []) -- No condition
clauseString xs (MkCond cond') = let (condstr, newxs) = evalCond xs cond' in
                                 (condstr , newxs)

clauseString xs (AND c1 c2) = let (clausestr, newxs) = clauseString xs c1 in
                              let (clausestr2, newxs') = clauseString newxs c2 in
                              (clausestr ++ " AND " ++ clausestr2 , newxs')

clauseString xs (OR c1 c2) = let (clausestr, newxs) = clauseString xs c1 in
                             let (clausestr2, newxs') = clauseString newxs c2 in
                             (clausestr ++ " OR " ++ clausestr2 , newxs')


-----------------------------------------------------------
-- | Evaluates conditional clauses.
-----------------------------------------------------------

condClauseStr : List (Maybe (Int, Value)) -> condClause -> (String, List (Maybe (Int, Value)))
condClauseStr xs (SET setcl) = let (condstr, newxs) = clauseString xs setcl in
                               (" SET " ++ condstr, newxs)

condClauseStr xs (WHERE setcl1 setcl2) = let (condstr, newxs) = condClauseStr xs setcl1 in
                                         let (condstr', newxs') = clauseString newxs setcl2 in
                                         ( condstr ++ " WHERE " ++ condstr', newxs')


-----------------------------------------------------------
-- | Evaluates queries by calling the other functions
-- on each part of the query
-----------------------------------------------------------
evalSQL : List (Maybe (Int, Value)) -> SQL -> (String, List (Maybe (Int, Value)))
-- SELECT data from tbl1 where num > (SELECT num from tbl1 where num = 24)
-- evalSQL [] ((SELECT ALL)(TBL "tbl")(MkSQL ((SELECT ALL) (TBL "tbl")(MkCond (VCol "))))
-- NTBF
--clauseString xs (MkSQL sql) = (evalSQL xs sql)

-- Separate list of tables
-- For complex type, return list returned by evalSQL
-- And add brackets
evalSQL xs (TBL tbl) = (unwords (intersperse "," ( tbl)), xs)
evalSQL xs (SELECT vars sql' c) =
    let (sqlstring, newxs) = evalSQL xs sql' in
    let (csstring, newxs') = clauseString newxs c in
    case c of
      Empty => case vars of
                 ALL => if complexType sql'
                          then ("SELECT " ++ "*" ++ " FROM " ++
                                putBrackets sqlstring ++ csstring,  newxs)
                          else ("SELECT " ++ "*" ++ " FROM " ++ sqlstring ++
                                csstring,  newxs')
                 Cols selvar => if complexType sql'
                                  then ("SELECT " ++ unwords selvar ++
                                        " FROM " ++ putBrackets sqlstring ++ csstring,  newxs)
                                  else ("SELECT " ++ unwords selvar ++ " FROM " ++ sqlstring ++
                                        csstring, newxs')
                 _  => case vars of
                         ALL => if complexType sql'
                                  then  ("SELECT " ++ "*" ++ " FROM " ++
                                         " WHERE " ++ csstring, newxs)
                                  else ("SELECT " ++ "*" ++ " FROM " ++  sqlstring
                                        ++ " WHERE " ++ csstring, newxs')
                         Cols selvar => if complexType sql'
                                          then ("SELECT " ++ (unwords selvar) ++ " FROM " ++
                                                putBrackets sqlstring  ++ " WHERE " ++
                                                csstring , newxs)
                                          else ("SELECT " ++ (unwords selvar) ++ " FROM " ++ sqlstring ++
                                                " WHERE " ++ csstring, newxs')


evalSQL xs (INSERT sql vals) = let (tblname, newvals) = evalSQL xs sql in
                               let (str, newxs ) = listVal newvals vals in
                               ("INSERT INTO " ++ tblname ++ " VALUES (" ++ str ++ ")", newxs)

evalSQL xs (INSERTC sql cols vals) = let (tblname, newvals) = evalSQL xs sql in
                                     let (strcol, newcol) = listVal newvals cols in
                                     let (strval, newcolval) = listVal newcol vals in
                                     ("INSERT INTO " ++ tblname ++ "(" ++ strcol ++ ")" ++ "VALUES (" ++  strval ++ ")", newcolval)


evalSQL xs (UPDATE sql cl) = let (tblname, newxs) = evalSQL xs sql in
                             let (csstring, newxs') = condClauseStr newxs cl in
                             ("UPDATE " ++ tblname ++ csstring, newxs')

evalSQL xs (CREATE sql details) = let (sqlstring, newxs) = evalSQL xs sql in
                                  let (csstring, newxs') = listValType newxs details in
                                  ("CREATE TABLE " ++ sqlstring ++ "(" ++ csstring ++ ")", newxs')
