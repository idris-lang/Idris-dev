import TestEx

area : Shape -> Double
area s with (shapeView s)
  area (triangle base height) | STriangle = 0.5 * base * height
  area (rectangle width height) | SRectangle = width * height
  area (circle radius) | SCircle = pi * radius * radius

main : IO ()
main = do printLn (area (rectangle 2 3))
          printLn (area (triangle 2 3))
          printLn (area (circle 1))
