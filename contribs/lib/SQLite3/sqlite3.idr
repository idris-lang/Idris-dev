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


data DB a = MkDB (IO (Either String a))

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
                         
                                                 

open_db : String -> IO DBPointer
open_db name = do x <- mkForeign (FFun "sqlite3_open_idr" [FString] FPtr)name
                  return (MkDBPointer x)

close_db : DBPointer -> IO Int
close_db (MkDBPointer pointer) =mkForeign (FFun "sqlite3_close_idr" [FPtr] FInt)pointer

                
exec_db : DBPointer  -> String -> DB Int
exec_db (MkDBPointer pointer) stmt = do 
        x <- liftIO(mkForeign (FFun "sqlite3_exec_idr" [FPtr, FString] FInt)pointer stmt)
        if (x /= 0)
            then fail "Could not execute."
                else return x
                                                            
get_error : DBPointer  -> IO String
get_error (MkDBPointer pointer) =mkForeign (FFun "sqlite3_get_error" [FPtr] FString)pointer

                               
prepare_db : DBPointer  -> String -> DB StmtPtr
prepare_db (MkDBPointer pointer) cmd = do

        result <- liftIO (mkForeign (FFun "sqlite3_prepare_idr" [FPtr, FString] FPtr)pointer cmd)
        flag <- liftIO(nullPtr result)
        if flag
            then fail "Error occured"
                else return (MkStmtPtr result)


step_db : StmtPtr -> DB Int
step_db (MkStmtPtr pointer) = do
         x <- liftIO (mkForeign (FFun "sqlite3_step_idr" [FPtr] FInt)pointer)
         if ( x == 101)
             then fail "SQLITE_DONE"
                 else return x


finalize_db : StmtPtr -> DB Int
finalize_db (MkStmtPtr pointer) = do 
        x <- liftIO (mkForeign (FFun "sqlite3_finalize_idr" [FPtr] FInt)pointer)
        if (x /= 0)
            then fail "Could not finalize"
                else return x

reset_db : StmtPtr  -> DB Int
reset_db (MkStmtPtr pointer) = do 
        x <- liftIO(mkForeign (FFun "sqlite3_reset_idr" [FPtr] FInt)pointer)
        if (x /=0)
            then fail "Could not reset"
                else return x

column_count : DBPointer  -> IO (Either String Int)
column_count (MkDBPointer pointer) = do 
        x <- mkForeign (FFun "sqlite3_column_count_idr" [FPtr] FInt)pointer
        if (x == 0 )
            then return (Left "No Data")
                 else return (Right x)

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



get_table : DBPointer -> String -> DB TBPointer
get_table (MkDBPointer pointer) name = do 
            x <- liftIO(mkForeign (FFun "sqlite3_get_table_idr" [FPtr, FString] FPtr)pointer name)
            flag <- liftIO(nullPtr x)
            if flag
                then  do x <- liftIO(get_error_table pointer) ; fail x                    
                     else return  (MkTBPointer x)
        where
            get_error_table : Ptr-> IO String
            get_error_table pointer = do x <- mkForeign (FFun "sqlite3_get_error" [FPtr] FString)pointer
                                         return x


num_row : TBPointer -> IO Int
num_row (MkTBPointer pointer) = do x <- mkForeign (FFun "sqlite3_get_num_row" [FPtr] FInt)pointer    
                                   return (x)

num_col : TBPointer -> IO Int
num_col (MkTBPointer pointer) = do x <- mkForeign (FFun "sqlite3_get_num_col" [FPtr] FInt)pointer
                                   return (x)
   

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
free_table (MkTBPointer pointer) = do x <- mkForeign (FFun "sqlite3_free_table_idr" [FPtr] FUnit)pointer
                                      return ()

		
toList : String -> String -> DBPointer -> DB Table
toList name stmt x =  do
    				ptr <- (get_table x (stmt))
    				nbR <- liftIO (num_row ptr)
    				nmC <- liftIO (num_col ptr)
    				res <- forM [0..(nbR-1)] (\ i =>
    					     forM [0..(nmC-1)] (\ j =>
    						         liftIO(get_data x name i j)
    				        )
    				)
    				liftIO (free_table ptr)
    				return res
    				

bind_int : StmtPtr -> Int -> Int -> DB Int
bind_int  (MkStmtPtr pointer) indexval val = do 
        x <- liftIO(mkForeign (FFun "sqlite3_bind_int_idr" [FPtr, FInt, FInt] FInt)pointer indexval val)                                   
        if (x /= 0 )
            then fail "Could not bind int."
                else return x                                             
                                 
                                 
bind_float : StmtPtr -> Int -> Int -> DB Int
bind_float (MkStmtPtr pointer) indexval val = do 
        x <- liftIO(mkForeign (FFun "sqlite3_bind_float_idr" [FPtr, FInt, FInt] FInt)pointer indexval val)
        if (x /= 0)
            then fail "Could not bind float."
                else return x 

bind_text :  StmtPtr -> String -> Int -> Int -> DB Int
bind_text (MkStmtPtr pointer) text indexval lengthval = do
         x <- liftIO(mkForeign (FFun "sqlite3_bind_text_idr" [FPtr, FString, FInt, FInt] FInt)pointer text indexval lengthval)
         if (x /= 0)
             then fail "Could not bind text."
                  else return x  

bind_null : StmtPtr -> Int -> DB Int
bind_null (MkStmtPtr pointer) indexval =do 
        x <- liftIO(mkForeign (FFun "sqlite3_bind_null_idr" [FPtr, FInt] FInt)pointer indexval)
        if (x /= 0)
             then fail "Could not bind null."
                 else return x
                
                
instance Show DBVal where
    show (DBInt i) = "Int val: " ++ show i
    show (DBText i) = "Text val: " ++ i
    show (DBFloat i) = "Float val: " ++ show i
    show (DBNull ) = "NULL"

print_data_v2 : DBVal -> String
print_data_v2 val = (show val)

test : DB()
test = do db <- liftIO (open_db "somedb.db")
          stmt <- (prepare_db db "insert into tbl1 values (?,?);")
          bind_int stmt 1 456
          bind_text stmt "testing" 2 4
          step_db stmt
          reset_db stmt
          finalize_db stmt
          c <- liftIO (close_db db)
          return ()  
          
test2 : DB ()
test2 = do db <- liftIO (open_db "somedb.db")
         
           tbl <- (get_table db "SELECT Student.Name FROM Student, Module, Enrollment WHERE Module.Credits = 30 AND Student.School_student = Enrollment.School_Student AND Student.School = Enrollment.School AND Enrollment.Code = Module.Code")
           --res <- (toList "Student" "select *from Student;" db)
          -- mydata <- liftIO ( get_data db "Student" 1 1)
       
           c <- liftIO (close_db db)
           return ()  
                                                                                                               
main : IO ()
main = do x <- runDB (test2) 
          --y <- runDB (test)
          return ()

       
