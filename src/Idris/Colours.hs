module Idris.Colours where

import System.Console.ANSI

-- Set the colour of a string using POSIX escape codes
colourise :: Color -> ColorIntensity -> String -> String
colourise c i str = let sgr = [SetColor Foreground i c]
                    in setSGRCode sgr ++ str ++ setSGRCode [Reset]

colouriseKwd :: String -> String
colouriseKwd kwd = setSGRCode [SetUnderlining SingleUnderline
                              , SetConsoleIntensity BoldIntensity
                              , SetColor Foreground Vivid Black
                              ] ++ kwd ++ setSGRCode [Reset]

colouriseBound :: String -> String
colouriseBound = colourise Magenta Vivid

colouriseImplicit :: String -> String
colouriseImplicit str = let sgr = [ SetColor Foreground Vivid Magenta
                                  , SetUnderlining SingleUnderline
                                  ]
                        in setSGRCode sgr ++ str ++ setSGRCode [Reset]

colouriseFun :: String -> String
colouriseFun = colourise Green Vivid

colouriseType :: String -> String
colouriseType = colourise Blue Vivid

colouriseData :: String -> String
colouriseData = colourise Red Vivid