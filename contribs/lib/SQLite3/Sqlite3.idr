module Sqlite3
import Sqlexpr


%lib C "sqlite3"
%link C "sqlite3api.o"
%include C "sqlite3api.h"

-----------------------------------------------------------------------------
-- |
-- Module      :  sqlite3
-- Copyright   :  (c) The University of St Andrews, 2012
--
-- Library built on top of FFI supporting basic SQLite C/C++ Interface
-- functions.
--
-----------------------------------------------------------------------------

-- | The types supported by Idris returned by the database functions.

data DBVal = DBInt Int
           | DBText String
           | DBFloat Float
           | DBNull

-- Database pointer
data DBPointer =  MkDBPointer Ptr
-- Table pointer
data TBPointer = MkTBPointer Ptr
-- Statement pointer
data StmtPtr = MkStmtPtr Ptr

Table : Type
Table = List (List DBVal)

-- ForMap used in to_list_v1
forM : Applicative f => List a -> (a -> f b) -> f (List b)
forM xs f = (sequence (map f xs))

-- Neater error handling done using DB
data DB a = MkDB (IO (Either String a))

instance Functor DB where
  fmap f (MkDB action) = MkDB (do res <- action
                                  return (fmap f res))


instance Applicative DB where
  pure = MkDB . return . Right
  (MkDB f) <$> (MkDB x) = MkDB (do f' <- f
                                   case f' of
                                     Left err => return (Left err)
                                     Right op => x >>= (return . fmap op))


instance Monad DB where
    (MkDB l) >>= k = MkDB (do c <- l
                              case c of
                                  Left err => return (Left err)
                                  Right v  => case k v of
                                                   MkDB k' => k')
    return x = MkDB (return (Right x))

fail : String -> DB a
fail err = MkDB (return (Left err))

liftIO : IO a -> DB a
liftIO f = MkDB (do f' <- f
                    return (Right f'))

ioError : String -> IO a
ioError err = do putStrLn err
                 return (believe_me ())

runDB : DB a -> IO a
runDB (MkDB f) = do f' <- f
                    case f' of
                         Right v => return v
                         Left str => ioError str

-----------------------------------------------------------------------------
-- | Opens an SQLite database file as specified by the String name argument.
-----------------------------------------------------------------------------

open_db : String -> DB DBPointer
open_db name = do x <- liftIO (mkForeign (FFun "sqlite3_open_idr" [FString] FPtr) name)
                  return (MkDBPointer x)

-----------------------------------------------------------------------------
-- | Destructor for the DBPointer.
-----------------------------------------------------------------------------

close_db : DBPointer -> DB Int
close_db (MkDBPointer pointer) = liftIO (mkForeign (FFun "sqlite3_close_idr" [FPtr] FInt) pointer)

-----------------------------------------------------------------------------
-- | Wrapper around prepare, step and finalize.
-----------------------------------------------------------------------------

exec_db : DBPointer  -> String -> DB Int
exec_db (MkDBPointer pointer) stmt = do
        x <- liftIO (mkForeign (FFun "sqlite3_exec_idr" [FPtr, FString] FInt) pointer stmt)
        if (x == 1)
          then fail "Could not execute."
          else return x

-----------------------------------------------------------------------------
-- | Executes a prepared query. Use of this version is recommended.
-----------------------------------------------------------------------------

exec_db_v2 : StmtPtr -> DB Int
exec_db_v2 (MkStmtPtr pointer) = do
        x <- liftIO (mkForeign (FFun "exec_db" [FPtr] FInt) pointer)
        if (x == 21)
          then fail "No data returned."
          else return x

-----------------------------------------------------------------------------
-- | Returns the error stored in the buffer by exec_db function.
-- This function can only be used with exec_db and get_table.
-- Only these functions store any occured error in the buffer array.
-----------------------------------------------------------------------------

get_error : DBPointer  -> IO String
get_error (MkDBPointer pointer) = mkForeign (FFun "sqlite3_get_error" [FPtr] FString) pointer


-----------------------------------------------------------------------------
-- | Compiles the query inot a byte-code program in order to execute it.
-- Returns a pointer to a Statement pointer on a successful call.
-- Returns a null pointer on a failure.
-----------------------------------------------------------------------------

prepare_db : DBPointer  -> String -> DB StmtPtr
prepare_db (MkDBPointer pointer) cmd = do
        result <- liftIO (mkForeign (FFun "sqlite3_prepare_idr" [FPtr, FString] FPtr) pointer cmd)
        flag <- liftIO (nullPtr result)
        if flag
          then fail "Error occured while preparing"
          else return (MkStmtPtr result)

-----------------------------------------------------------------------------
-- | Returns the error stored in the buffer by exec_db function.
-- This function can only be used with exec_db and get_table.
-- Only these functions store any occured error in the buffer array.
-----------------------------------------------------------------------------

step_db : StmtPtr -> DB Int
step_db (MkStmtPtr pointer)= do
         x <- liftIO (mkForeign (FFun "sqlite3_step_idr" [FPtr] FInt)pointer)
         if ( x == 101)
           then fail "SQLITE_DONE"
           else return x

-----------------------------------------------------------------------------
-- | Deletes a prepared statement. This function must be called after
-- prepare function.
-----------------------------------------------------------------------------

finalize_db : StmtPtr -> DB Int
finalize_db (MkStmtPtr pointer) = do
        x <- liftIO (mkForeign (FFun "sqlite3_finalize_idr" [FPtr] FInt) pointer)
        if (x /= 0)
          then fail "Could not finalize"
          else return x

-----------------------------------------------------------------------------
-- | Resets a prepared statement pointer back to its initial state.
-----------------------------------------------------------------------------

reset_db : StmtPtr  -> DB Int
reset_db (MkStmtPtr pointer) = do
        x <- liftIO (mkForeign (FFun "sqlite3_reset_idr" [FPtr] FInt) pointer)
        if (x /= 0)
          then fail "Could not reset"
          else return x

-----------------------------------------------------------------------------
-- | These routines obtain column information.
-----------------------------------------------------------------------------

column_count : DBPointer  -> IO (Either String Int)
column_count (MkDBPointer pointer) = do
        x <- mkForeign (FFun "sqlite3_column_count_idr" [FPtr] FInt) pointer
        return $ if (x == 0 )
                   then Left "No Data"
                   else (Right x)

column_name : DBPointer  -> Int -> IO String
column_name (MkDBPointer pointer) iCol =
        mkForeign (FFun "sqlite3_column_name_idr" [FPtr, FInt] FString) pointer iCol

column_decltype : DBPointer  -> Int -> IO String
column_decltype (MkDBPointer pointer) iCol =
        mkForeign (FFun "sqlite3_column_decltype_idr" [FPtr, FInt] FString) pointer iCol


column_bytes : DBPointer -> Int -> IO Int
column_bytes (MkDBPointer pointer) iCol =
        mkForeign (FFun "sqlite3_column_bytes_idr" [FPtr, FInt] FInt) pointer iCol


column_blob : DBPointer  -> Int -> IO String
column_blob (MkDBPointer pointer) iCol =
        mkForeign (FFun "sqlite3_column_bytes_idr" [FPtr, FInt] FString) pointer iCol


column_text : DBPointer  -> Int -> IO String
column_text (MkDBPointer pointer) iCol =
        mkForeign (FFun "sqlite3_column_text_idr" [FPtr, FInt] FString) pointer iCol


column_Int : DBPointer  -> Int -> IO Int
column_Int (MkDBPointer pointer) iCol =
        mkForeign (FFun "sqlite3_column_int_idr" [FPtr, FInt] FInt) pointer iCol

-----------------------------------------------------------------------------
-- | These routines support some of SQLite backup functions.
-----------------------------------------------------------------------------

backup_init : DBPointer -> String -> DBPointer -> String -> IO DBPointer
backup_init (MkDBPointer des_pointer) destName (MkDBPointer src_pointer) srcName =
        do x <- mkForeign (FFun "sqlite3_backup_init_idr" [FPtr,FString, FPtr, FString] FPtr)
                          des_pointer destName src_pointer srcName
           return (MkDBPointer x)

backup_step : DBPointer -> Int -> IO Int
backup_step (MkDBPointer pointer) nPage =
        mkForeign (FFun "sqlite3_backup_step_idr" [FPtr, FInt] FInt) pointer nPage

backup_finish : DBPointer -> IO Int
backup_finish (MkDBPointer pointer) =
        mkForeign (FFun "sqlite3_backup_finish_idr" [FPtr] FInt) pointer

backup_remaining : DBPointer -> IO Int
backup_remaining (MkDBPointer pointer) =
        mkForeign (FFun "sqlite3_backup_remaining_idr" [FPtr] FInt) pointer


-----------------------------------------------------------------------------
-- |  Use of this interface is not recommended.
-- This function returns a result table. The functions num_row and num_col
-- are used to obtain the number of rows and columns.
-- These functions can be used to print the resulting table.
-----------------------------------------------------------------------------

get_table : DBPointer -> String -> DB TBPointer
get_table (MkDBPointer pointer) name = do
            x <- liftIO(mkForeign (FFun "sqlite3_get_table_idr" [FPtr, FString] FPtr) pointer name)
            flag <- liftIO (nullPtr x)
            if flag
              then do x <- liftIO(get_error_table pointer) ; fail x
              else return (MkTBPointer x)
        where
            get_error_table : Ptr-> IO String
            get_error_table pointer = do x <- mkForeign (FFun "sqlite3_get_error" [FPtr] FString) pointer
                                         return x


free_table : TBPointer -> IO ()
free_table (MkTBPointer pointer) = do x <- mkForeign (FFun "sqlite3_free_table_idr" [FPtr] FUnit) pointer
                                      return ()

-----------------------------------------------------------------------------
-- |  This version of these function obtain the row and column number
-- from the Table struct. These functions are only used with get_table.
-----------------------------------------------------------------------------

num_row : TBPointer -> IO Int
num_row (MkTBPointer pointer) = do x <- mkForeign (FFun "sqlite3_get_num_row" [FPtr] FInt) pointer
                                   return x

num_col : TBPointer -> IO Int
num_col (MkTBPointer pointer) = do x <- mkForeign (FFun "sqlite3_get_num_col" [FPtr] FInt) pointer
                                   return x

-----------------------------------------------------------------------------
-- |  This version of these function obtain the row and column number
-- from the Database struct.
-----------------------------------------------------------------------------

num_row_v2 : DBPointer -> IO Int
num_row_v2 (MkDBPointer pointer) = do x <- mkForeign (FFun "sqlite3_get_num_row_v2" [FPtr] FInt) pointer
                                      return x

num_col_v2 : DBPointer -> IO Int
num_col_v2 (MkDBPointer pointer) = do x <- mkForeign (FFun "sqlite3_get_num_col_v2" [FPtr] FInt) pointer
                                      return x

-----------------------------------------------------------------------------
-- | This function prints the result of a query by checking the type
-- of each value returned, it then calls the appropriate function.
-- Ther result is one of the DBVal variants.
-----------------------------------------------------------------------------

get_data : DBPointer -> Int -> Int -> IO DBVal
get_data (MkDBPointer pointer) row col = do
    ty <- get_data_type pointer row col
    helper ty
   where get_data_type : Ptr ->Int -> Int -> IO Int
         get_data_type pointer row col =
             mkForeign (FFun "sqlite3_get_data_type" [FPtr, FInt, FInt] FInt) pointer row col
         get_data_val_int : Ptr  -> Int -> IO Int
         get_data_val_int pointer col =
             mkForeign (FFun "sqlite3_get_val_int" [FPtr,FInt] FInt) pointer col

         get_data_val_text : Ptr -> Int -> IO String
         get_data_val_text pointer col =
             mkForeign (FFun "sqlite3_get_val_text" [FPtr, FInt] FString) pointer col

         get_data_val_float : Ptr -> Int -> IO Float
         get_data_val_float pointer col =
             mkForeign (FFun "sqlite3_get_float" [FPtr, FInt] FFloat) pointer col

         helper : Int -> IO DBVal
         helper 1 = do i <- get_data_val_int pointer col ; return (DBInt i)
         helper 2 = do i <- get_data_val_float pointer col ; return (DBFloat i)
         helper 3 = do i <- get_data_val_text pointer col; return (DBText i)
         helper _ = return DBNull

-----------------------------------------------------------------------------
-- | This function makes use of get_data to get all the result.
-----------------------------------------------------------------------------

toList_v1 : DBPointer -> DB Table
toList_v1 db = do nbR <- liftIO (num_row_v2 db)
                  nmC <- liftIO (num_col_v2 db)
                  res <- liftIO $ forM [0..(nbR-1)] $ \ i =>
                                    forM [0..(nmC-1)] $ \ j => get_data db i j
                  return (the (List (List DBVal)) res)

strcat : String -> String-> String
strcat str1 str2 = str1 ++ str2

-----------------------------------------------------------------------------
-- | This version of toList retunrs result from get_table
-- This could be removed if not needed in the future.
-----------------------------------------------------------------------------

--toList_v2 : String -> String -> DBPointer -> DB Table
--toList_v2 name stmt x =  do
--    				       ptr <- (get_table x (stmt))
--    				       nbR <- liftIO (num_row ptr)
--    				       nmC <- liftIO (num_col ptr)
--    				       res <- forM [0..(nbR-1)] (\ i =>
--    					            forM [0..(nmC-1)] (\ j =>
--    						                liftIO(get_data x name i j)
--
--    				               )
--    				       )
--    				       liftIO (free_table ptr)
--    				       return res


-----------------------------------------------------------------------------
-- | These routines support binding the types supported by Idris.
-- These return a pointer to statement pointer since we want to allow
-- binding multiple values by implementing a recursive function.
-----------------------------------------------------------------------------

bind_int : StmtPtr -> Int -> Int -> DB StmtPtr
bind_int (MkStmtPtr pointer) indexval val = do
        x <- liftIO (mkForeign (FFun "sqlite3_bind_int_idr" [FPtr, FInt, FInt] FPtr) pointer indexval val)
        flag <- liftIO (nullPtr x)
        if flag
          then fail "Could not bind int."
          else return (MkStmtPtr x)


bind_float : StmtPtr -> Int -> Float -> DB StmtPtr
bind_float (MkStmtPtr pointer) indexval val = do
        x <- liftIO (mkForeign (FFun "sqlite3_bind_float_idr" [FPtr, FInt, FFloat] FPtr) pointer indexval val)
        flag <- liftIO (nullPtr x)
        if flag
          then fail "Could not bind float."
          else return (MkStmtPtr x)

bind_text :  StmtPtr -> String -> Int -> Int -> DB StmtPtr
bind_text (MkStmtPtr pointer) text indexval lengthval = do
         x <- liftIO (mkForeign (FFun "sqlite3_bind_text_idr" [FPtr, FString, FInt, FInt] FPtr)
                                pointer text indexval lengthval)
         flag <- liftIO(nullPtr x)
         if flag
           then fail "Could not bind text."
           else return (MkStmtPtr x)

bind_null : StmtPtr -> Int -> DB StmtPtr
bind_null (MkStmtPtr pointer) indexval = do
        x <- liftIO (mkForeign (FFun "sqlite3_bind_null_idr" [FPtr, FInt] FPtr) pointer indexval)
        flag <- liftIO (nullPtr x)
        if flag
          then fail "Could not bind null."
          else return (MkStmtPtr x)

-----------------------------------------------------------------------------
-- | String Length
-----------------------------------------------------------------------------

strlen : String -> DB Int
strlen str = liftIO (mkForeign (FFun "strLength" [FString] FInt) str)

instance Show DBVal where
    show (DBInt i)   = "Int val: "   ++ show i ++ "\n"
    show (DBText i)  = "Text val: "  ++ show i ++ "\n"
    show (DBFloat i) = "Float val: " ++ show i ++ "\n"
    show (DBNull )   = "NULL"

-----------------------------------------------------------------------------
-- | Multi bind a list of values.
-----------------------------------------------------------------------------

bindMulti : StmtPtr-> List (Maybe (Int, Value)) -> DB StmtPtr
bindMulti pointer [] = return pointer
bindMulti pointer (Nothing :: vs) = bindMulti pointer vs
bindMulti pointer ((Just (indexs, (VInt i)))::vs) =
    do x <- bind_int pointer indexs i
       bindMulti x vs
bindMulti pointer ((Just (indexs, (VStr s)))::vs) =
    do len <- strlen s
       x <- bind_text pointer s indexs len
       bindMulti x vs
bindMulti pointer ((Just (indexs, (VFloat f)))::vs) =
    do x <- bind_float pointer indexs f
       bindMulti x vs

