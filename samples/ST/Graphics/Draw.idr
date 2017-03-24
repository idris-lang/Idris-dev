module Draw

import public Graphics.SDL
import Control.ST
import Control.ST.ImplicitCall

%access public export

data Col = MkCol Int Int Int Int

black : Col 
black = MkCol 0 0 0 255

red : Col 
red = MkCol 255 0 0 255

green : Col 
green = MkCol 0 255 0 255

blue : Col 
blue = MkCol 0 0 255 255

cyan : Col 
cyan = MkCol 0 255 255 255

magenta : Col 
magenta = MkCol 255 0 255 255

yellow : Col 
yellow = MkCol 255 255 0 255

white : Col 
white = MkCol 255 255 255 255

interface Draw (m : Type -> Type) where
  Surface : Type

  initWindow : Int -> Int -> ST m (Maybe Var) [addIfJust Surface]
  closeWindow : (win : Var) -> ST m () [remove win Surface] 

  flip : (win : Var) -> ST m () [win ::: Surface]
  poll : ST m (Maybe Event) []

  filledRectangle : (win : Var) -> (Int, Int) -> (Int, Int) -> Col ->
                    ST m () [win ::: Surface]
  drawLine : (win : Var) -> (Int, Int) -> (Int, Int) -> Col ->
             ST m () [win ::: Surface]


Draw IO where
  Surface = State SDLSurface

  initWindow x y = do Just srf <- lift (startSDL x y)
                           | pure Nothing
                      var <- new srf
                      pure (Just var)

  closeWindow win = do lift endSDL
                       delete win

  flip win = do srf <- read win
                lift (flipBuffers srf)
  poll = lift pollEvent

  filledRectangle win (x, y) (ex, ey) (MkCol r g b a)
       = do srf <- read win
            lift $ filledRect srf x y ex ey r g b a
  drawLine win (x, y) (ex, ey) (MkCol r g b a)
       = do srf <- read win
            lift $ drawLine srf x y ex ey r g b a

render : Draw m => (win : Var) -> ST m () [win ::: Surface {m}]
render win = do filledRectangle win (0,0) (640,480) black
                drawLine win (100,100) (200,200) red
                flip win
    
loop : Draw m => (win : Var) -> ST m () [win ::: Surface {m}]
loop win = do render win
              Just AppQuit <- poll
                   | _ => loop win
              pure ()

drawMain : (ConsoleIO m, Draw m) => ST m () []
drawMain = do Just win <- initWindow 640 480
                 | Nothing => putStrLn "Can't open window"
              loop win
              closeWindow win

