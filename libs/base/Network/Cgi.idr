module Network.Cgi

import System

%default total

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
    MkCGI : (CGIInfo -> IO (a, CGIInfo)) -> CGI a

getAction : CGI a -> CGIInfo -> IO (a, CGIInfo)
getAction (MkCGI act) = act

instance Functor CGI where
    f <$> (MkCGI c) = MkCGI (\s => do (a, i) <- c s
                                      return (f a, i))

instance Applicative CGI where
    pure v = MkCGI (\s => return (v, s))

    (MkCGI a) <*> (MkCGI b) = MkCGI (\s => do (f, i) <- a s
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
lift : IO a -> CGI a
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

getContent : Int -> IO String
getContent x = getC (toNat x) "" where
    getC : Nat -> String -> IO String
    getC Z     acc = return $ reverse acc
    getC (S k) acc = do x <- getChar
                        getC k (strCons x acc)

getCgiEnv : String -> IO String
getCgiEnv key = do
  val <- getEnv key
  return $ maybe "" id val

abstract
runCGI : CGI a -> IO a
runCGI prog = do
    clen_in <- getCgiEnv "CONTENT_LENGTH"
    let clen = prim__fromStrInt clen_in
    content <- getContent clen
    query   <- getCgiEnv "QUERY_STRING"
    cookie  <- getCgiEnv "HTTP_COOKIE"
    agent   <- getCgiEnv "HTTP_USER_AGENT"

    let get_vars  = getVars ['&',';'] query
    let post_vars = getVars ['&'] content
    let cookies   = getVars [';'] cookie

    (v, st) <- getAction prog (CGISt get_vars post_vars cookies agent
                 "Content-type: text/html\n"
                 "")
    putStrLn (Headers st)
    putStr (Output st)
    return v


