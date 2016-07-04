{-# LANGUAGE CPP #-}
module Main where

import Control.Monad
import Data.Char
import Data.List
import Data.Maybe
import qualified Data.Set as S
import Data.Time.Clock
import System.Directory
import System.Environment
import System.FilePath
import System.Exit
import System.Info
import System.IO
import System.Process

-- Because GHC earlier than 7.8 lacks setEnv
-- Install the setenv package on Windows.
#if __GLASGOW_HASKELL__ < 708
#ifndef mingw32_HOST_OS
import qualified System.Posix.Env as PE(setEnv)

setEnv k v = PE.setEnv k v True
#else
import System.SetEnv(setEnv)
#endif
#endif

data Flag = Update | Diff | ShowOutput | Quiet | Time deriving (Eq, Show, Ord)

type Flags = S.Set Flag

data Status = Success | Failure | Updated deriving (Eq, Show)

data Config = Config {
    flags :: Flags,
    idrOpts :: [String],
    tests :: [String]
} deriving (Show, Eq)

isQuiet conf = Quiet `S.member` (flags conf)
showOutput conf = ShowOutput `S.member` (flags conf)
showTime conf = Time  `S.member` (flags conf)
showDiff conf = Diff `S.member` (flags conf)
doUpdate conf = Update  `S.member` (flags conf)

checkTestName :: String -> Bool
checkTestName d = (all isDigit $ take 3 $ reverse d)
                    && (not $ isInfixOf "disabled" d)

enumTests :: IO [String]
enumTests = do
    cwd <- getCurrentDirectory
    dirs <- getDirectoryContents cwd
    return $ sort $ filter checkTestName dirs

parseFlag :: String -> Maybe Flag
parseFlag s = case s of
    "-u" -> Just Update
    "-d" -> Just Diff
    "-s" -> Just ShowOutput
    "-t" -> Just Time
    "-q" -> Just Quiet
    _    -> Nothing

parseFlags :: [String] -> (S.Set Flag, [String])
parseFlags xs = (S.fromList f, i)
    where
        f = catMaybes $ map parseFlag fl
        (fl, i) = partition (\s -> parseFlag s /= Nothing) xs

parseArgs :: [String] -> IO Config
parseArgs args = do
    (tests, rest) <- case args of
        ("all":xs) -> do
            et <- enumTests
            return (et, xs)
        ("without":xs) -> do
            t <- enumTests
            (blacklist, ys) <- return $ break (== "opts") xs
            return (t \\ blacklist, ys \\ ["opts"])
        (x:xs) -> do
            exists <- doesDirectoryExist x
            return (if checkTestName x && exists then [x] else [], xs)
        [] -> do
            et <- enumTests
            return (et, [])
    let (testOpts, idOpts) = parseFlags rest
    return $ Config testOpts idOpts tests

-- "bash" needed because Haskell has cmd as the default shell on windows, and
-- we also want to run the process with another current directory, so we get
-- this thing.
runInShell :: String -> [String] -> IO (ExitCode, String)
runInShell test opts = do
    (ec, output, _) <- readCreateProcessWithExitCode
                            ((proc "bash" ("run":opts)) { cwd = Just test,
                                                          std_out = CreatePipe })
                            ""
    return (ec, output)

runTest :: Config -> String -> IO Status
runTest conf test = do
    -- don't touch the current directory as we want to run these things
    -- in parallel in the future
    let inTest s = test ++ "/" ++ s
    t1 <- getCurrentTime
    (exitCode, output) <- runInShell test (idrOpts conf)
    t2 <- getCurrentTime
    expected <- readFile $ inTest "expected"
    writeFile (inTest "output") output
    res <- if (norm output == norm expected)
                then do putStrLn $ test ++ " finished...success"
                        return Success
                else if doUpdate conf
                    then do putStrLn $ test ++ " finished...UPDATE"
                            writeFile (inTest "expected") output
                            return Updated
                    else do putStrLn $ test ++ " finished...FAILURE"
                            _ <- rawSystem "diff" [inTest "output", inTest "expected"]
                            return Failure
    when (showTime conf) $ do
        let dt = diffUTCTime t2 t1
        putStrLn $ "Duration of " ++ test ++ " was " ++ show dt
    return res
  where 
    -- just pretend that backslashes are slashes for comparison
    -- purposes to avoid path problems, so don't write any tests
    -- that depend on that distinction in other contexts.
    -- Also rewrite newlines for consistency.
       norm ('\r':'\n':xs) = '\n' : norm xs
       norm ('\\':'\\':xs) = '/' : norm xs
       norm ('\\':xs) = '/' : norm xs
       norm (x : xs) = x : norm xs
       norm [] = []

printStats :: Config -> [Status] -> IO ()
printStats conf stats = do
    let total = length stats
    let successful = length $ filter (== Success) stats
    let failures = length $ filter (== Failure) stats
    let updates = length $ filter (== Updated) stats
    putStrLn "\n----"
    putStrLn $ show total ++ " tests run: " ++ show successful ++ " succesful, "
                ++ show failures ++ " failed, " ++ show updates ++ " updated."
    let failed = map fst $ filter ((== Failure) . snd) $ zip (tests conf) stats
    when (failed /= []) $ do
        putStrLn "\nFailed tests:"
        mapM_ putStrLn failed
        putStrLn ""

runTests :: Config -> IO Bool
runTests conf = do
    stats <- mapM (runTest conf) (tests conf)
    unless (isQuiet conf) $ printStats conf stats
    return $ all (== Success) stats

runShow :: Config -> IO Bool
runShow conf = do
    mapM_ (\t -> callProcess "cat" [t++"/output"]) (tests conf)
    return True

runDiff :: Config -> IO Bool
runDiff conf = do
    mapM_ (\t -> do putStrLn $ "Differences in " ++ t ++ ":"
                    ec <- rawSystem "diff" [t++"/output", t++"/expected"]
                    when (ec == ExitSuccess) $ putStrLn "No differences found.")
          (tests conf)
    return True

whisper :: Config -> String -> IO ()
whisper conf s = do unless (isQuiet conf) $ putStrLn s

isWindows :: Bool
isWindows = os `elem` ["win32", "mingw32", "cygwin32"]

setPath :: Config -> IO ()
setPath conf = do
    maybeEnv <- lookupEnv "IDRIS"
    idrisExists <- case maybeEnv of
        Just idrisExe -> do
            let exeExtension = if isWindows then ".exe" else ""
            doesFileExist (idrisExe ++ exeExtension)
        Nothing -> return False
    if (idrisExists)
        then do
            idrisAbs <- makeAbsolute $ fromMaybe "" maybeEnv
            setEnv "IDRIS" idrisAbs
            whisper conf $ "Using " ++ idrisAbs
        else do
            path <- getEnv "PATH"
            setEnv "IDRIS" ""
            let sandbox = "../.cabal-sandbox/bin"
            hasBox <- doesDirectoryExist sandbox
            bindir <- if hasBox
                            then do
                                whisper conf $ "Using Cabal sandbox at " ++ sandbox
                                makeAbsolute sandbox
                            else do
                                stackExe <- findExecutable "stack"
                                case stackExe of
                                    Just stack -> do
                                        out <- readProcess stack ["path", "--dist-dir"] []
                                        stackDistDir <- return $ takeWhile (/= '\n') out
                                        let stackDir = "../" ++ stackDistDir ++ "/build/idris"
                                        whisper conf $ "Using stack work dir at " ++ stackDir
                                        makeAbsolute stackDir
                                    Nothing -> return ""
            when (bindir /= "") $ setEnv "PATH" (bindir ++ [searchPathSeparator] ++ path)

main = do
    hSetBuffering stdout LineBuffering
    withCabal <- doesDirectoryExist "test"
    when withCabal $ do
      setCurrentDirectory "test"
    args <- getArgs
    conf <- parseArgs args
    setPath conf
    t1 <- getCurrentTime
    res <- case tests conf of
                [] -> return True
                xs | showOutput conf -> runShow conf
                xs | showDiff conf -> runDiff conf
                xs -> runTests conf
    t2 <- getCurrentTime
    when (showTime conf) $ do
        let dt = diffUTCTime t2 t1
        putStrLn $ "Duration of Entire Test Suite was " ++ show dt
    unless res exitFailure
