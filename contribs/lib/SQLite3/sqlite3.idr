module main
%lib "sqlite3"
%link "sqlite3api.o"
%include "sqlite3api.h"

data DBVal = DBInt Int
           | DBText String
           | DBFloat Float
           | DBNull

data DBPointer =  MkDBPointer Ptr

data TBPointer = MkTBPointer Ptr

data StmtPtr = MkStmtPtr Ptr
				
Table : Set
Table = List (List DBVal)


forM : Monad m => List a -> (a -> m b) -> m (List b)
forM f xs = mapM xs f


open_db : String -> IO DBPointer
open_db name = do x <- mkForeign (FFun "sqlite3_open_idr" [FString] FPtr)name
                  return (MkDBPointer x)

close_db : DBPointer -> IO Int
close_db (MkDBPointer pointer) =mkForeign (FFun "sqlite3_close_idr" [FPtr] FInt)pointer


exec_db : DBPointer  -> String -> IO Int
exec_db (MkDBPointer pointer) stmt =mkForeign (FFun "sqlite3_exec_idr" [FPtr, FString] FInt)pointer stmt

get_error : DBPointer  -> IO String
get_error (MkDBPointer pointer) =mkForeign (FFun "sqlite3_get_error" [FPtr] FString)pointer

prepare_db : DBPointer  -> String -> IO (Either String StmtPtr)
prepare_db (MkDBPointer pointer) cmd = do

        result <- mkForeign (FFun "sqlite3_prepare_idr" [FPtr, FString] FPtr)pointer cmd
        flag <- nullPtr result
        if flag
            then return (Left "Error occured")
                else return (Right (MkStmtPtr result))

step_db : Either String StmtPtr -> IO (Either String Int)
step_db (Right (MkStmtPtr pointer)) = do x <- mkForeign (FFun "sqlite3_step_idr" [FPtr] FInt)pointer
                                         return (Right (x))
                                            
step_db (Left erro) = return (Left "Error in step")                                          


finalize_db : Either String StmtPtr -> IO (Either String Int)
finalize_db (Right (MkStmtPtr pointer)) = do x <- mkForeign (FFun "sqlite3_finalize_idr" [FPtr] FInt)pointer
                                             return (Right (x))
finalize_db (Left erro) = return (Left "Error while finalizing") 

reset_db : Either String StmtPtr  -> IO (Either String Int)
reset_db (Right (MkStmtPtr pointer)) = do x <- mkForeign (FFun "sqlite3_reset_idr" [FPtr] FInt)pointer
                                          return (Right (x))
reset_db (Left erro) = return (Left "Error while resetting") 

column_count : DBPointer  -> IO Int
column_count (MkDBPointer pointer) =mkForeign (FFun "sqlite3_column_count_idr" [FPtr] FInt)pointer

column_name : DBPointer  -> Int -> IO String
column_name (MkDBPointer pointer) iCol =mkForeign (FFun "sqlite3_column_name_idr" [FPtr, FInt] FString)pointer iCol

column_decltype : DBPointer  -> Int -> IO String
column_decltype (MkDBPointer pointer) iCol =mkForeign (FFun "sqlite3_column_decltype_idr" [FPtr, FInt] FString)pointer iCol


column_bytes : DBPointer -> Int -> IO Int
column_bytes (MkDBPointer pointer) iCol =mkForeign (FFun "sqlite3_column_bytes_idr" [FPtr, FInt] FInt)pointer iCol


column_blob : DBPointer  -> Int -> IO String
column_blob (MkDBPointer pointer) iCol =mkForeign (FFun "sqlite3_column_bytes_idr" [FPtr, FInt] FString)pointer iCol


column_text : DBPointer  -> Int -> IO String
column_text (MkDBPointer pointer) iCol =mkForeign (FFun "sqlite3_column_text_idr" [FPtr, FInt] FString)pointer iCol


column_Int : DBPointer  -> Int -> IO Int
column_Int (MkDBPointer pointer) iCol =mkForeign (FFun "sqlite3_column_int_idr" [FPtr, FInt] FInt)pointer iCol


backup_init : DBPointer -> String -> DBPointer -> String -> IO DBPointer 
backup_init (MkDBPointer des_pointer) destName (MkDBPointer src_pointer) srcName = do x <- mkForeign (FFun "sqlite3_backup_init_idr" [FPtr,FString, FPtr, FString] FPtr)des_pointer destName src_pointer srcName
                                                                                      return (MkDBPointer x)

backup_step : DBPointer -> Int -> IO Int
backup_step (MkDBPointer pointer) nPage =mkForeign (FFun "sqlite3_backup_step_idr" [FPtr, FInt] FInt)pointer nPage

backup_finish : DBPointer -> IO Int
backup_finish (MkDBPointer pointer) =mkForeign (FFun "sqlite3_backup_finish_idr" [FPtr] FInt)pointer

backup_remaining : DBPointer -> IO Int
backup_remaining (MkDBPointer pointer) =mkForeign (FFun "sqlite3_backup_remaining_idr" [FPtr] FInt)pointer

get_table : DBPointer -> String -> IO TBPointer
get_table (MkDBPointer pointer) name = do x <- mkForeign (FFun "sqlite3_get_table_idr" [FPtr, FString]  FPtr)pointer name
                                          return (MkTBPointer x)

num_row : TBPointer -> IO Int
num_row (MkTBPointer pointer) = mkForeign (FFun "sqlite3_get_num_row" [FPtr] FInt)pointer

num_col : TBPointer -> IO Int
num_col (MkTBPointer pointer) = mkForeign (FFun "sqlite3_get_num_col" [FPtr] FInt)pointer

get_data : DBPointer -> String -> Int -> Int -> IO DBVal
get_data (MkDBPointer pointer) tbl_name row col = do
    ty <- get_data_type pointer tbl_name row col
    helper ty
   where
		get_data_type      : Ptr -> String -> Int -> Int -> IO Int
		get_data_type pointer tbl_name row col =mkForeign (FFun "sqlite3_get_data_type" [FPtr, FString, FInt, FInt] FInt)pointer tbl_name row col
		
		get_data_val_int   : Ptr -> String -> Int -> Int  -> IO Int
		get_data_val_int pointer tbl_name row col =mkForeign (FFun "sqlite3_get_val_int" [FPtr, FString, FInt, FInt] FInt)pointer tbl_name row col
		
		get_data_val_text  : Ptr -> String -> Int -> Int -> IO String
		get_data_val_text pointer tbl_name row col =mkForeign (FFun "sqlite3_get_val_text" [FPtr, FString, FInt, FInt] FString)pointer tbl_name row col
		
		get_data_val_float : Ptr -> String -> Int -> Int -> IO Float
		get_data_val_float pointer tbl_name row col =mkForeign (FFun "sqlite3_get_float" [FPtr, FString, FInt, FInt] FFloat)pointer tbl_name row col


		helper : Int -> IO DBVal
		helper 1 = do i <- get_data_val_int pointer tbl_name row col; return (DBInt i)
		helper 2 = do i <- get_data_val_float pointer tbl_name row col; return (DBFloat i)
		helper 3 = do i <- get_data_val_text pointer tbl_name row col; return (DBText i)
		helper _ = return (DBNull)

		            
strcat : String -> String-> String
strcat str1 str2 = (str1 ++ str2)		

free_table : TBPointer -> IO ()
free_table (MkTBPointer pointer) =mkForeign (FFun "sqlite3_free_table_idr" [FPtr] FUnit)pointer
		
toList : String -> String -> DBPointer -> IO Table
toList name stmt x =  do
    				ptr <- get_table x (stmt)
    				nbR <- num_row ptr
    				nmC <- num_col ptr
    				res <- forM [0..(nbR-1)] (\ i =>
    					   forM [0..(nmC-1)] (\ j =>
    						get_data x name i j
    					)
    				)
    				free_table ptr
    				return res
    				
bind_int : Either String StmtPtr -> Int -> Int -> IO (Either String Int)
bind_int (Right (MkStmtPtr pointer)) indexval val = do x <- mkForeign (FFun "sqlite3_bind_int_idr" [FPtr, FInt, FInt] FInt)pointer indexval val                                   
                                                       return (Right x)

bind_int (Left erro) indexval val = return (Left "Could not bind int.")

bind_float : Either String StmtPtr -> Int -> Int -> IO (Either String Int)
bind_float (Right (MkStmtPtr pointer)) indexval val = do x <- mkForeign (FFun "sqlite3_bind_float_idr" [FPtr, FInt, FInt] FInt)pointer indexval val
                                                         return (Right x) 

bind_float (Left erro) indexval val = return (Left "Could not bind float.")		

bind_text : Either String StmtPtr -> String -> Int -> Int -> IO (Either String Int)
bind_text (Right (MkStmtPtr pointer)) text indexval lengthval = do x <- mkForeign (FFun "sqlite3_bind_text_idr" [FPtr, FString, FInt, FInt] FInt)pointer text indexval lengthval
                                                                   return (Right x)
                                                                   
bind_text (Left erro) text indexval lengthval = return (Left "Could not bind text.")  

bind_null : Either String StmtPtr -> Int -> IO (Either String Int)
bind_null (Right (MkStmtPtr pointer)) indexval =do x <- mkForeign (FFun "sqlite3_bind_null_idr" [FPtr, FInt] FInt)pointer indexval
                                                   return (Right x)
                                                   
bind_null (Left erro) indexval = return (Left "Could not bind null.")  


-- May need some alterations

print_data : (Show DBVal) => String -> DBVal -> String -> Int -> Int -> IO String
print_data  dbname val tblname dig1 dig2 = do x <- open_db dbname
                                              val <- get_data x tblname 1 0
                                              close_db x
                                              return (show val)

-- Some simple test cases
                                          
test : IO ()
test = do x <- open_db "somedb.db"
          stmt <- prepare_db x "SELECT * FROM tbl1 WHERE data='test2'"
          f <- step_db stmt
          finalize_db stmt
          close_db x
          return ()
          
test2 : IO ()
test2 = do x <- open_db "somedb.db"
           tbl <- get_table x "SELECT * FROM tbl1 WHERE num =44'"
           free_table tbl
           close_db x
           return ()          

test3 : IO ()
test3 = do x <- open_db "somedb.db"
           e <- open_db "./newdb.db"
           tbl <- get_table x "SELECT * FROM tbl1;"
           tbl2 <- get_table x "SELECT * FROM mytable ;" 
           free_table tbl
           free_table tbl2
           close_db x
           close_db e
           return ()
           
test4 : IO ()
test4 = do x <- open_db "somedb.db"
           somedata <- get_data x "tbl1" 1 0
           mylist <- toList "tbl1" "SELECT * FROM tbl1 WHERE data='test4'"  x        
           close_db x
           return ()            
                                                                                                               
main : IO ()
main = do x <- test4
          return ()

       
