module Control.ST.ImplicitCall

import Control.ST

||| Make 'call' implicit.
||| This makes ST programs less verbose, at the cost of making error messages
||| potentially more difficult to read.
export implicit
imp_call : STrans m t ys ys' ->
       {auto ctxt_prf : SubCtxt ys xs} ->
       STrans m t xs (\res => updateWith (ys' res) xs ctxt_prf)
imp_call = call

