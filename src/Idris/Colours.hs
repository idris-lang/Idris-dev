module Idris.Colours (
  IdrisColour(..),
  ColourTheme(..),
  defaultTheme,
  colouriseKwd, colouriseBound, colouriseImplicit,
  colouriseType, colouriseFun, colouriseData, colouriseKeyword,
  colourisePrompt, colourise, ColourType(..)) where

import System.Console.ANSI

data IdrisColour = IdrisColour { colour    :: Maybe Color
                               , vivid     :: Bool
                               , underline :: Bool
                               , bold      :: Bool
                               , italic    :: Bool
                               }
                   deriving (Eq, Show)

mkColour :: Color -> IdrisColour
mkColour c = IdrisColour (Just c) True False False False

data ColourTheme = ColourTheme { keywordColour  :: IdrisColour
                               , boundVarColour :: IdrisColour
                               , implicitColour :: IdrisColour
                               , functionColour :: IdrisColour
                               , typeColour     :: IdrisColour
                               , dataColour     :: IdrisColour
                               , promptColour   :: IdrisColour
                               }
                   deriving (Eq, Show)

-- | Idris's default console colour theme
defaultTheme :: ColourTheme
defaultTheme = ColourTheme { keywordColour = IdrisColour Nothing True False True False
                           , boundVarColour = mkColour Magenta
                           , implicitColour = IdrisColour (Just Magenta) True True False False
                           , functionColour = mkColour Green
                           , typeColour = mkColour Blue
                           , dataColour = mkColour Red
                           , promptColour = IdrisColour Nothing True False True False
                           }

-- | Set the colour of a string using POSIX escape codes
colourise :: IdrisColour -> String -> String
colourise (IdrisColour c v u b i) str = setSGRCode sgr ++ str ++ setSGRCode [Reset]
    where sgr = fg c ++
                (if u then [SetUnderlining SingleUnderline] else []) ++
                (if b then [SetConsoleIntensity BoldIntensity] else []) ++
                (if i then [SetItalicized True] else [])
          fg Nothing = []
          fg (Just c) = [SetColor Foreground (if v then Vivid else Dull) c]

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

colouriseKeyword :: ColourTheme -> String -> String
colouriseKeyword t = colourise (keywordColour t)

data ColourType = KeywordColour
                | BoundVarColour
                | ImplicitColour
                | FunctionColour
                | TypeColour
                | DataColour
                | PromptColour
                  deriving (Eq, Show, Bounded, Enum)
