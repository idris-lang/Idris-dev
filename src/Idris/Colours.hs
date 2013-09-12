module Idris.Colours where

import System.Console.ANSI

data IdrisColour = IdrisColour { colour    :: Color
                               , vivid     :: Bool
                               , underline :: Bool
                               , bold      :: Bool
                               }

mkColour :: Color -> IdrisColour
mkColour c = IdrisColour c True False False

data ColourTheme = ColourTheme { keywordColour  :: IdrisColour
                               , boundVarColour :: IdrisColour
                               , implicitColour :: IdrisColour
                               , functionColour :: IdrisColour
                               , typeColour     :: IdrisColour
                               , dataColour     :: IdrisColour
                               }

defaultTheme :: ColourTheme
defaultTheme = ColourTheme { keywordColour = IdrisColour Black True True True
                           , boundVarColour = mkColour Magenta
                           , implicitColour = IdrisColour Magenta True True False
                           , functionColour = mkColour Green
                           , typeColour = mkColour Blue
                           , dataColour = mkColour Red
                           }

-- Set the colour of a string using POSIX escape codes
colourise :: IdrisColour -> String -> String
colourise (IdrisColour c v u b) str = setSGRCode sgr ++ str ++ setSGRCode [Reset]
    where sgr = [SetColor Foreground (if v then Vivid else Dull) c] ++
                (if u then [SetUnderlining SingleUnderline] else []) ++
                (if b then [SetConsoleIntensity BoldIntensity] else [])

colouriseKwd :: String -> String
colouriseKwd = colourise (keywordColour defaultTheme)

colouriseBound :: String -> String
colouriseBound = colourise (boundVarColour defaultTheme)

colouriseImplicit :: String -> String
colouriseImplicit = colourise (implicitColour defaultTheme)

colouriseFun :: String -> String
colouriseFun = colourise (functionColour defaultTheme)

colouriseType :: String -> String
colouriseType = colourise (typeColour defaultTheme)

colouriseData :: String -> String
colouriseData = colourise (dataColour defaultTheme)