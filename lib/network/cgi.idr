module network.cgi;

import system;

public
Vars : Set;
Vars = List (String, String);

data CGIInfo = CGISt Vars -- GET
                     Vars -- POST
                     Vars -- Cookies
                     String -- User agent
                     String -- headers
                     String; -- output

get_GET : CGIInfo -> Vars;
get_GET (CGISt g _ _ _ _ _) = g;

get_POST : CGIInfo -> Vars;
get_POST (CGISt _ p _ _ _ _) = p;

get_Cookies : CGIInfo -> Vars;
get_Cookies (CGISt _ _ c _ _ _) = c;

get_UAgent : CGIInfo -> String;
get_UAgent (CGISt _ _ _ a _ _) = a;

get_Headers : CGIInfo -> String;
get_Headers (CGISt _ _ _ _ h _) = h;

get_Output : CGIInfo -> String;
get_Output (CGISt _ _ _ _ _ o) = o;

add_Headers : String -> CGIInfo -> CGIInfo;
add_Headers str (CGISt g p c a h o) = CGISt g p c a (h ++ str) o;

add_Output : String -> CGIInfo -> CGIInfo;
add_Output str (CGISt g p c a h o) = CGISt g p c a h (o ++ str);

abstract
data CGI : Set -> Set where
    MkCGI : (CGIInfo -> IO (a, CGIInfo)) -> CGI a;

getAction : CGI a -> CGIInfo -> IO (a, CGIInfo);
getAction (MkCGI act) = act;

instance Monad CGI where {
    (>>=) (MkCGI f) k = MkCGI (\s => do { v <- f s;
                                          getAction (k (fst v)) (snd v); });

    return v = MkCGI (\s => return (v, s));
}

setInfo : CGIInfo -> CGI ();
setInfo i = MkCGI (\s => return ((), i));

getInfo : CGI CGIInfo;
getInfo = MkCGI (\s => return (s, s));

abstract
lift : IO a -> CGI a ;
lift op = MkCGI (\st => do { x <- op;
                             return (x, st); } ); 

abstract
output : String -> CGI ();
output s = do { i <- getInfo;
                setInfo (add_Output s i); };

abstract
queryVars : CGI Vars;
queryVars = do { i <- getInfo;
                 return (get_GET i); };

abstract
postVars : CGI Vars;
postVars = do { i <- getInfo;
                return (get_POST i); };

abstract
cookieVars : CGI Vars;
cookieVars = do { i <- getInfo;
                  return (get_Cookies i); };

abstract
queryVar : String -> CGI (Maybe String);
queryVar x = do { vs <- queryVars;
                  return (lookup x vs); };

getOutput : CGI String;
getOutput = do { i <- getInfo;
                 return (get_Output i); };

getHeaders : CGI String;
getHeaders = do { i <- getInfo;
                  return (get_Headers i); };

abstract
flushHeaders : CGI ();
flushHeaders = do { o <- getHeaders;
                    lift (putStrLn o);
                  };

abstract
flush : CGI ();
flush = do { o <- getOutput;
             lift (putStr o);
           };

getVars : List Char -> String -> List (String, String);
getVars seps query = mapMaybe readVar (split (\x => elem x seps) query) 
  where {
    readVar : String -> Maybe (String, String);
    readVar xs with split (\x => x == '=') xs {
        | [k, v] = Just (trim k, trim v);
        | _      = Nothing;
    }
  }

getContent : Int -> IO String;
getContent x = getC x "" where {
    getC : Int -> String -> IO String;
    getC 0 acc = return $ rev acc;
    getC n acc = do { x <- getChar;
                      getC (n-1) (strCons x acc); };
}

abstract
runCGI : CGI a -> IO a;
runCGI prog = do {
    clen_in <- getEnv "CONTENT_LENGTH";
    let clen = prim__strToInt clen_in;
    content <- getContent clen;
    query   <- getEnv "QUERY_STRING";
    cookie  <- getEnv "HTTP_COOKIE";
    agent   <- getEnv "HTTP_USER_AGENT";

    let get_vars  = getVars ['&',';'] query;
    let post_vars = getVars ['&'] content;
    let cookies   = getVars [';'] cookie;

    p <- getAction prog (CGISt get_vars post_vars cookies agent 
            "Content-type: text/html\n" 
            "");
    putStrLn (get_Headers (snd p));
    putStr (get_Output (snd p));
    return (fst p);
};





