module Network.Cgi

import System

public
Vars : Set
Vars = List (String, String)

record CGIInfo : Set where
       CGISt : (GET : Vars) ->
               (POST : Vars) ->
               (Cookies : Vars) ->
               (UserAgent : String) ->
               (Headers : String) ->
               (Output : String) -> CGIInfo

add_Headers : String -> CGIInfo -> CGIInfo
add_Headers str st = record { Headers = Headers st ++ str } st

add_Output : String -> CGIInfo -> CGIInfo
add_Output str st = record { Output = Output st ++ str } st

abstract
data CGI : Set -> Set where
    MkCGI : (CGIInfo -> IO (a, CGIInfo)) -> CGI a

getAction : CGI a -> CGIInfo -> IO (a, CGIInfo)
getAction (MkCGI act) = act

instance Functor CGI where
    fmap f (MkCGI c) = MkCGI (\s => do (a, i) <- c s
                                       pure (f a, i))

instance Applicative CGI where
    pure v = MkCGI (\s => pure (v, s))
    
    (MkCGI a) <$> (MkCGI b) = MkCGI (\s => do (f, i) <- a s
                                              (c, j) <- b i
                                              pure (f c, j))

instance Monad CGI where {
    (>>=) (MkCGI f) k = MkCGI (\s => do v <- f s
                                        getAction (k (fst v)) (snd v))
}

setInfo : CGIInfo -> CGI ()
setInfo i = MkCGI (\s => pure ((), i))

getInfo : CGI CGIInfo
getInfo = MkCGI (\s => pure (s, s))

abstract
lift : IO a -> CGI a 
lift op = MkCGI (\st => do { x <- op
                             pure (x, st) } ) 

abstract
output : String -> CGI ()
output s = do i <- getInfo
              setInfo (add_Output s i)

abstract
queryVars : CGI Vars
queryVars = do i <- getInfo
               pure (GET i)

abstract
postVars : CGI Vars
postVars = do i <- getInfo
              pure (POST i)

abstract
cookieVars : CGI Vars
cookieVars = do i <- getInfo
                pure (Cookies i)

abstract
queryVar : String -> CGI (Maybe String)
queryVar x = do vs <- queryVars
                pure (lookup x vs)

getOutput : CGI String
getOutput = do i <- getInfo
               pure (Output i)

getHeaders : CGI String
getHeaders = do i <- getInfo
                pure (Headers i)

abstract
flushHeaders : CGI ()
flushHeaders = do o <- getHeaders
                  lift (putStrLn o)

abstract
flush : CGI ()
flush = do o <- getOutput
           lift (putStr o) 

getVars : List Char -> String -> List (String, String)
getVars seps query = mapMaybe readVar (split (\x => elem x seps) query) 
  where
    readVar : String -> Maybe (String, String)
    readVar xs with (split (\x => x == '=') xs)
        | [k, v] = Just (trim k, trim v)
        | _      = Nothing

getContent : Int -> IO String
getContent x = getC x "" where
    %assert_total
    getC : Int -> String -> IO String
    getC 0 acc = pure $ reverse acc
    getC n acc = if (n > 0)
                    then do x <- getChar
                            getC (n-1) (strCons x acc)
                    else (return "")

abstract
runCGI : CGI a -> IO a
runCGI prog = do 
    clen_in <- getEnv "CONTENT_LENGTH"
    let clen = prim__strToInt clen_in
    content <- getContent clen
    query   <- getEnv "QUERY_STRING"
    cookie  <- getEnv "HTTP_COOKIE"
    agent   <- getEnv "HTTP_USER_AGENT"

    let get_vars  = getVars ['&',';'] query
    let post_vars = getVars ['&'] content
    let cookies   = getVars [';'] cookie

    (v, st) <- getAction prog (CGISt get_vars post_vars cookies agent 
                 "Content-type: text/html\n" 
                 "")
    putStrLn (Headers st)
    putStr (Output st)
    pure v


