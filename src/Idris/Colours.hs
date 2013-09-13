module Idris.Colours (
  IdrisColour(..),
  ColourTheme(..),
  defaultTheme,
  colouriseKwd, colouriseBound, colouriseImplicit,
  colouriseType, colouriseFun, colouriseData,
  colourisePrompt,
  ColourType(..)) where

import System.Console.ANSI

data IdrisColour = IdrisColour { colour    :: Color
                               , vivid     :: Bool
                               , underline :: Bool
                               , bold      :: Bool
                               }
                   deriving (Eq, Show)

mkColour :: Color -> IdrisColour
mkColour c = IdrisColour c True False False

data ColourTheme = ColourTheme { keywordColour  :: IdrisColour
                               , boundVarColour :: IdrisColour
                               , implicitColour :: IdrisColour
                               , functionColour :: IdrisColour
                               , typeColour     :: IdrisColour
                               , dataColour     :: IdrisColour
                               , promptColour   :: IdrisColour
                               }
                   deriving (Eq, Show)

defaultTheme :: ColourTheme
defaultTheme = ColourTheme { keywordColour = IdrisColour Black True True True
                           , boundVarColour = mkColour Magenta
                           , implicitColour = IdrisColour Magenta True True False
                           , functionColour = mkColour Green
                           , typeColour = mkColour Blue
                           , dataColour = mkColour Red
                           , promptColour = IdrisColour Black True False True
                           }

-- Set the colour of a string using POSIX escape codes
colourise :: IdrisColour -> String -> String
colourise (IdrisColour c v u b) str = setSGRCode sgr ++ str ++ setSGRCode [Reset]
    where sgr = [SetColor Foreground (if v then Vivid else Dull) c] ++
                (if u then [SetUnderlining SingleUnderline] else []) ++
                (if b then [SetConsoleIntensity BoldIntensity] else [])

colouriseKwd :: ColourTheme -> String -> String
colouriseKwd t = colourise (keywordColour t)

colouriseBound :: ColourTheme -> String -> String
colouriseBound t = colourise (boundVarColour t)

colouriseImplicit :: ColourTheme -> String -> String
colouriseImplicit t = colourise (implicitColour t)

colouriseFun :: ColourTheme -> String -> String
colouriseFun t = colourise (functionColour t)

colouriseType :: ColourTheme -> String -> String
colouriseType t = colourise (typeColour t)

colouriseData :: ColourTheme -> String -> String
colouriseData t = colourise (dataColour t)

colourisePrompt :: ColourTheme -> String -> String
colourisePrompt t = colourise (promptColour t)


data ColourType = KeywordColour
                | BoundVarColour
                | ImplicitColour
                | FunctionColour
                | TypeColour
                | DataColour
                | PromptColour
                  deriving (Eq, Show, Bounded, Enum)
