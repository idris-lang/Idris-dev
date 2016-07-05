{-# LANGUAGE DeriveGeneric #-}
{-|
Module      : Idris.Colours
Description : Support for colours within Idris.
Copyright   :
License     : BSD3
Maintainer  : The Idris Community.
-}
module Idris.Colours (
    IdrisColour(..)
  , ColourTheme(..)
  , defaultTheme
  , colouriseKwd, colouriseBound, colouriseImplicit, colourisePostulate
  , colouriseType, colouriseFun, colouriseData, colouriseKeyword
  , colourisePrompt, colourise, ColourType(..), hStartColourise, hEndColourise
  ) where

import GHC.Generics (Generic)
import System.Console.ANSI
import System.IO (Handle)

data IdrisColour = IdrisColour { colour    :: Maybe Color
                               , vivid     :: Bool
                               , underline :: Bool
                               , bold      :: Bool
                               , italic    :: Bool
                               }
                   deriving (Eq, Show)

mkColour :: Color -> IdrisColour
mkColour c = IdrisColour (Just c) True False False False

data ColourTheme = ColourTheme { keywordColour   :: IdrisColour
                               , boundVarColour  :: IdrisColour
                               , implicitColour  :: IdrisColour
                               , functionColour  :: IdrisColour
                               , typeColour      :: IdrisColour
                               , dataColour      :: IdrisColour
                               , promptColour    :: IdrisColour
                               , postulateColour :: IdrisColour
                               }
                   deriving (Eq, Show, Generic)

-- | Idris's default console colour theme
defaultTheme :: ColourTheme
defaultTheme = ColourTheme { keywordColour = IdrisColour Nothing True False True False
                           , boundVarColour = mkColour Magenta
                           , implicitColour = IdrisColour (Just Magenta) True True False False
                           , functionColour = mkColour Green
                           , typeColour = mkColour Blue
                           , dataColour = mkColour Red
                           , promptColour = IdrisColour Nothing True False True False
                           , postulateColour = IdrisColour (Just Green) True False True False
                           }

-- | Compute the ANSI colours corresponding to an Idris colour
mkSGR :: IdrisColour -> [SGR]
mkSGR (IdrisColour c v u b i) =
    fg c ++
    [SetUnderlining SingleUnderline | u] ++
    [SetConsoleIntensity BoldIntensity | b] ++
    [SetItalicized True | i]
  where
    fg Nothing = []
    fg (Just c) = [SetColor Foreground (if v then Vivid else Dull) c]

-- | Set the colour of a string using POSIX escape codes
colourise :: IdrisColour -> String -> String
colourise c str = setSGRCode (mkSGR c) ++ str ++ setSGRCode [Reset]

-- | Start a colour on a handle, to support colour output on Windows
hStartColourise :: Handle -> IdrisColour -> IO ()
hStartColourise h c = hSetSGR h (mkSGR c)

-- | End a colour region on a handle
hEndColourise :: Handle -> IdrisColour -> IO ()
hEndColourise h _ = hSetSGR h [Reset]

-- | Set the colour of a string using POSIX escape codes, with trailing '\STX' denoting the end
-- (required by Haskeline in the prompt string)
colouriseWithSTX :: IdrisColour -> String -> String
colouriseWithSTX (IdrisColour c v u b i) str = setSGRCode sgr ++ "\STX" ++ str ++ setSGRCode [Reset] ++ "\STX"
    where sgr = fg c ++
                [SetUnderlining SingleUnderline | u] ++
                [SetConsoleIntensity BoldIntensity | b] ++
                [SetItalicized True | i]
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
colourisePrompt t = colouriseWithSTX (promptColour t)

colouriseKeyword :: ColourTheme -> String -> String
colouriseKeyword t = colourise (keywordColour t)

colourisePostulate :: ColourTheme -> String -> String
colourisePostulate t = colourise (postulateColour t)


data ColourType = KeywordColour
                | BoundVarColour
                | ImplicitColour
                | FunctionColour
                | TypeColour
                | DataColour
                | PromptColour
                | PostulateColour
                  deriving (Eq, Show, Bounded, Enum)
