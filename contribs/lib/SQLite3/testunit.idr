module main
import sqlite3

          
testexpr : DB()
testexpr = do db <- open_db "somedb.db"
              let sql = (evalSQL [] ((SELECT ALL)(TBL "tbl1")  (OR (AND (MkCond (Equals (VCol "data")(VStr "data0"))) (MkCond (Equals (VCol "num")(VInt 1))) )  (MkCond (Equals (VCol "num")(VInt 2))))))
              let x = (fst sql)
              let list = (snd sql)
              liftIO(print x)
              stmt <- (prepare_db db x)
              bindMulti stmt list 
              exec_db_v2 stmt 
              res <- toList db
              liftIO(print res)          
              finalize_db stmt
              close_db db
              return ()

testupdate : DB()
testupdate = do db <- open_db "somedb.db"
                let sql = (evalSQL [] (UPDATE (TBL "tbl1") (WHERE (SET (MkCond (Equals(VCol "data") (VStr "data0"))) ) (MkCond (Equals (VCol "num") (VInt 2))) ) ))
                let x = (fst sql)
                let list = (snd sql)
                liftIO(print x)
                stmt <- (prepare_db db x)
                bindMulti stmt list 
                exec_db_v2 stmt           
                finalize_db stmt
                close_db db
                return ()

testInsert : DB()
testInsert = do db <- open_db "somedb.db"
                let sql = (evalSQL [] (INSERT (TBL "tbl1") [(VInt 2),(VStr "histring2")]))
                let x = (fst sql)
                let list = (snd sql)
                liftIO(print x)
                stmt <- (prepare_db db x)
                bindMulti stmt list 
                exec_db_v2 stmt          
                finalize_db stmt
                close_db db
                return ()  
                
testNull : DB()
testNull = do db <- open_db "somedb.db"
              let sql = (evalSQL [] ((SELECT ALL)(TBL "tbl1") (MkCond (MkNULL (VCol "data")))))
              let x = (fst sql)
              let list = (snd sql)
              liftIO(print x)
              stmt <- (prepare_db db x)
              bindMulti stmt list 
              exec_db_v2 stmt
              res <- toList db
              liftIO(print res)           
              finalize_db stmt
              close_db db
              return ()     

                           
testInsertWithCond : DB()
testInsertWithCond = do db <- open_db "somedb.db"
                        let sql = (evalSQL [] (INSERTC (TBL "tbl1") [(VCol "data"),(VCol "num")] [(VInt 201),(VStr "newinserted")]))
                        let x = (fst sql)
                        let list = (snd sql)
                        liftIO(print x)
                        stmt <- (prepare_db db x)
                        bindMulti stmt list 
                        exec_db_v2 stmt           
                        finalize_db stmt
                        close_db db
                        return ()                  
                                
-- Nested queries need to have the same column as the outer queries !!!
testNestedSel1 : DB()
testNestedSel1 = do db <- open_db "somedb.db"
                    let sql = (evalSQL [] (SELECT (Cols ["data"]) (SELECT (Cols["num","data"]) (TBL "tbl1") (MkCond (Equals (VCol "num")(VInt 2))) )   Empty   ) )
                    let x = (fst sql)
                    let list = (snd sql)
                    liftIO(print x)
                    stmt <- (prepare_db db x)
                    bindMulti stmt list 
                    exec_db_v2 stmt 
                    res <- toList db
                    liftIO(print res)           
                    finalize_db stmt
                    close_db db
                    return ()                                                                                                                                

-- Testing Create Table
testCreateTable : DB ()
testCreateTable =  do db <- open_db "somedb.db"
                      let sql = (evalSQL [] (CREATE (TBL "mynewtbl") [ ((VCol "col"),(CInt "int"),(None)) ] ) )
                      let x = (fst sql)
                      let list = (snd sql)
                      liftIO(print x)
                      stmt <- (prepare_db db x)
                      bindMulti stmt list 
                      exec_db_v2 stmt           
                      finalize_db stmt
                      close_db db
                      return () 

main : IO ()
main = do --x <- runDB (test3) 
          y <- runDB (testNestedSel1)
          return ()
