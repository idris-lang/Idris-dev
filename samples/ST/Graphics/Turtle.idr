module Main

import Control.ST
import Control.ST.ImplicitCall
import Draw

interface TurtleGraphics (m : Type -> Type) where
  Turtle : Type

  start : Int -> Int -> ST m (Maybe Var) [addIfJust Turtle]
  end : (t : Var) -> ST m () [Remove t Turtle]

  fd : (t : Var) -> Int -> ST m () [t ::: Turtle]
  rt : (t : Var) -> Int -> ST m () [t ::: Turtle]

  penup : (t : Var) -> ST m () [t ::: Turtle]
  pendown : (t : Var) -> ST m () [t ::: Turtle]
  col : (t : Var) -> Col -> ST m () [t ::: Turtle]

  -- Render the picture drawn so far in a window, and wait for a key press
  render : (t : Var) -> ST m () [t ::: Turtle]

Line : Type
Line = ((Int, Int), (Int, Int), Col)

-- Implement turtle graphics in terms of existing stateful systems;
-- 'Draw' provides a Surface to draw on, and three states.
Draw m => TurtleGraphics m where
  Turtle = Composite [Surface {m}, -- surface to draw on
                      State Col,  -- pen colour
                      State (Int, Int, Int, Bool), -- pen location/direction/down
                      State (List Line)] -- lines to draw on render

  start x y = with ST do 
                 Just srf <- initWindow x y
                      | Nothing => pure Nothing
                 col <- new white
                 pos <- new (320, 200, 0, True)
                 lines <- new []
                 turtle <- new ()
                 combine turtle [srf, col, pos, lines]
                 pure (Just turtle)

  end t = do [srf, col, pos, lines] <- split t
             closeWindow srf; delete col; delete pos; delete lines; delete t

  fd t dist = with ST do 
                 [srf, col, pos, lines] <- split t
                 (x, y, d, p) <- read pos
                 let x' = cast x + cast dist * sin (rad d)
                 let y' = cast y + cast dist * cos (rad d)
                 c <- read col
                 ls <- read lines
                 write lines (if p then ((x, y), (cast x', cast y'), c) :: ls
                                   else ls)
                 write pos (cast x', cast y', d, p)
                 combine t [srf, col, pos, lines]
     where rad : Int -> Double
           rad x = (cast x * pi) / 180.0

  rt t angle = with ST do 
                  [srf, col, pos, lines] <- split t
                  (x, y, d, p) <- read pos
                  write pos (x, y, d + angle `mod` 360, p)
                  combine t [srf, col, pos, lines]

  penup t = with ST do 
               [srf, col, pos, lines] <- split t
               (x, y, d, _) <- read pos
               write pos (x, y, d, False)
               combine t [srf, col, pos, lines]
  pendown t = with ST do 
                 [srf, col, pos, lines] <- split t
                 (x, y, d, _) <- read pos
                 write pos (x, y, d, True)
                 combine t [srf, col, pos, lines]
  col t c = with ST do 
               [srf, col, pos, lines] <- split t
               write col c
               combine t [srf, col, pos, lines]

  render t = with ST do 
                [srf, col, pos, lines] <- split t
                filledRectangle srf (0, 0) (640, 480) black
                drawAll srf !(read lines)
                flip srf
                combine t [srf, col, pos, lines]
                Just ev <- poll
                  | Nothing => render t
                case ev of
                     KeyUp _ => pure ()
                     _ => render t
   where drawAll : (srf : Var) -> List Line -> ST m () [srf ::: Surface {m}]
         drawAll srf [] = pure ()
         drawAll srf ((start, end, col) :: xs) 
            = do drawLine srf start end col
                 drawAll srf xs

turtle : (ConsoleIO m, TurtleGraphics m) => ST m () []
turtle = with ST do 
            Just t <- start 640 480
                 | Nothing => putStr "Can't make turtle\n"
            col t yellow
            fd t 100; rt t 90
            col t green
            fd t 100; rt t 90
            col t red
            fd t 100; rt t 90
            col t blue
            fd t 100; rt t 90
            render t
            end t

main : IO ()
main = run turtle

