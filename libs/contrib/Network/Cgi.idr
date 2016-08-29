module Network.Cgi

import System

%default total

public export
Vars : Type
Vars = List (String, String)

record CGIInfo where
  constructor CGISt
  GET : Vars
  POST : Vars
  Cookies : Vars
  UserAgent : String
  Headers : String
  Output : String

add_Headers : String -> CGIInfo -> CGIInfo
add_Headers str st = record { Headers = Headers st ++ str } st

add_Output : String -> CGIInfo -> CGIInfo
add_Output str st = record { Output = Output st ++ str } st

export
data CGI : Type -> Type where
    MkCGI : (CGIInfo -> IO (a, CGIInfo)) -> CGI a

getAction : CGI a -> CGIInfo -> IO (a, CGIInfo)
getAction (MkCGI act) = act

implementation Functor CGI where
    map f (MkCGI c) = MkCGI (\s => do (a, i) <- c s
                                      pure (f a, i))

implementation Applicative CGI where
    pure v = MkCGI (\s => pure (v, s))

    (MkCGI a) <*> (MkCGI b) = MkCGI (\s => do (f, i) <- a s
                                              (c, j) <- b i
                                              pure (f c, j))

implementation Monad CGI where
    (>>=) (MkCGI f) k = MkCGI (\s => do v <- f s
                                        getAction (k (fst v)) (snd v))

setInfo : CGIInfo -> CGI ()
setInfo i = MkCGI (\s => pure ((), i))

getInfo : CGI CGIInfo
getInfo = MkCGI (\s => pure (s, s))

export
lift : IO a -> CGI a
lift op = MkCGI (\st => do { x <- op
                             pure (x, st) } )

export
output : String -> CGI ()
output s = do i <- getInfo
              setInfo (add_Output s i)

export
queryVars : CGI Vars
queryVars = do i <- getInfo
               pure (GET i)

export
postVars : CGI Vars
postVars = do i <- getInfo
              pure (POST i)

export
cookieVars : CGI Vars
cookieVars = do i <- getInfo
                pure (Cookies i)

export
queryVar : String -> CGI (Maybe String)
queryVar x = do vs <- queryVars
                pure (lookup x vs)

getOutput : CGI String
getOutput = do i <- getInfo
               pure (Output i)

getHeaders : CGI String
getHeaders = do i <- getInfo
                pure (Headers i)

export
flushHeaders : CGI ()
flushHeaders = do o <- getHeaders
                  lift (putStrLn o)

export
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
getContent x = getC (cast x) "" where
    getC : Nat -> String -> IO String
    getC Z     acc = pure $ reverse acc
    getC (S k) acc = do x <- getChar
                        getC k (strCons x acc)

getCgiEnv : String -> IO String
getCgiEnv key = do
  val <- getEnv key
  pure $ maybe "" id val

export
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
    pure v


