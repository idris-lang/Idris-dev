module Main

import CFFI

string_from_c : Ptr -> IO String
string_from_c str = foreign FFI_C "make_string_2" (Ptr -> IO String) str

connection_information_struct : Composite
connection_information_struct = STRUCT [I8, PTR, PTR, PTR, I32]

send_page : (conn : Ptr) -> (text : String) -> (code : Int) -> IO Int
send_page conn page code = pure (the Int 1)

-- Error here was using the error from the 'do' block without 'Delay' applied,
-- which ended up looking very strange... elaborator should take the first
-- error (from the delayed block) when elaborating arguments which may or may
-- not need a delay
answer_to_connection : Ptr -> Ptr -> IO Int
answer_to_connection conn conn_info = do
  code_fld <- pure $ (connection_information_struct#4) conn_info
  code <- peek I32 code_fld
  answer_fld <- pure $ (connection_information_struct#1) conn_info
  answer <- peek PTR answer_fld
  if answer /= null then do
      str <- string_from_c answer
      send_page conn str code -- (prim__zextB32_Int code)
    else do
      send_page conn str (prim__zextB32_Int code)

