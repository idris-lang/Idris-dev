module Network.Cgi

import System

public
Vars : Type
Vars = List (String, String)

record CGIInfo : Type where
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
data CGI : Type -> Type where
    MkCGI : (CGIInfo -> UnsafeIO (a, CGIInfo)) -> CGI a

getAction : CGI a -> CGIInfo -> UnsafeIO (a, CGIInfo)
getAction (MkCGI act) = act

instance Functor CGI where
    map f (MkCGI c) = MkCGI (\s => do (a, i) <- c s
                                      return (f a, i))

instance Applicative CGI where
    pure v = MkCGI (\s => return (v, s))
    
    (MkCGI a) <$> (MkCGI b) = MkCGI (\s => do (f, i) <- a s
                                              (c, j) <- b i
                                              return (f c, j))

instance Monad CGI where {
    (>>=) (MkCGI f) k = MkCGI (\s => do v <- f s
                                        getAction (k (fst v)) (snd v))
}

setInfo : CGIInfo -> CGI ()
setInfo i = MkCGI (\s => return ((), i))

getInfo : CGI CGIInfo
getInfo = MkCGI (\s => return (s, s))

abstract
lift : UnsafeIO a -> CGI a 
lift op = MkCGI (\st => do { x <- op
                             return (x, st) } ) 

abstract
output : String -> CGI ()
output s = do i <- getInfo
              setInfo (add_Output s i)

abstract
queryVars : CGI Vars
queryVars = do i <- getInfo
               return (GET i)

abstract
postVars : CGI Vars
postVars = do i <- getInfo
              return (POST i)

abstract
cookieVars : CGI Vars
cookieVars = do i <- getInfo
                return (Cookies i)

abstract
queryVar : String -> CGI (Maybe String)
queryVar x = do vs <- queryVars
                return (lookup x vs)

getOutput : CGI String
getOutput = do i <- getInfo
               return (Output i)

getHeaders : CGI String
getHeaders = do i <- getInfo
                return (Headers i)

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

getContent : Int -> UnsafeIO String
getContent x = getC x "" where
    %assert_total
    getC : Int -> String -> UnsafeIO String
    getC 0 acc = return $ reverse acc
    getC n acc = if (n > 0)
                    then do x <- getChar
                            getC (n-1) (strCons x acc)
                    else (return "")

abstract
runCGI : CGI a -> UnsafeIO a
runCGI prog = do 
    clen_in <- getEnv "CONTENT_LENGTH"
    let clen = prim__fromStrInt clen_in
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
    return v


