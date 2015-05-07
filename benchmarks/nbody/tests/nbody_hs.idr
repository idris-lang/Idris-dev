import Data.Floats
import Effect.State
import System

offsetMomentum : (Float, Float, Float) -> Planet -> Planet 
offsetMomentum (px,py,pz) planet = record { vx = -px / m, vy = -py / m, vz = -pz / m } planet
  where m = mass planet

init : Integral n => (n, n, n) -> n -> (n, n, n)
init (px,py,pz) i = do
    if i >= length planets
        then return (px,py,pz)
        else runPureInit [ p_s := index i planets ] $ do
            p <- p_s :- get
            init (px + vx p * mass p, py + vy p * mass p, pz + vz p * mass p) (i+1)

run : Int -> Vect n $ { [STATE Planet] } Eff m () -> IO ()
run i p = case i of
    Z => return ()
    S _ => do
      advance p
      run (i-1) p

advance : Vect n $ { [STATE Planet] } Eff m () -> IO ()
advance planets = do
    advance' 0
    advance'' 0
    return () 
        
advance' : Integer -> IO ()
advance' i = when (i < length planets) $ do
  loop (i+1)

loop : Integer -> IO ()
loop j = when (j < length planets) $ 
         runPureInit [ ii := index i planets, jj := index j planets ] $ do
           ii_p <- ii :- get
           jj_p <- jj :- get
           let dx = the Float $ x ii_p - x jj_p
           let dy = the Float $ y ii_p - y jj_p
           let dz = the Float $ z ii_p - z jj_p {- Measure distance between planets -}  
           let dSquared = the Float $ squared dx dy dz
           let magnitude = the Float $ dt / (dSquared * sqrt dSquared)   
           ii :- update $ point (-) jj_p {- Point planets at each other -}
           jj :- update $ point (+) ii_p
           loop (j+1)

point : (a -> a -> a) -> Planet -> Planet -> Planet
point f planet_2 planet_1 = record{ vx = f $ vx planet_1 (dx * mass planet_2 * magnitude),
                                    vy = f $ vy planet_1 (dy * mass planet_2 * magnitude),
                                    vz = f $ vz planet_1 (dz * mass planet_2 * magnitude)} planet_1

advance'' : Integer -> IO ()
advance'' i = when (i < length planets) $
              runPureInit [p_s := index i planets] $ do
                p_s :- update move
                advance'' (i+1)

move : Planet -> Planet
move planet = record{ x = x planet + dt * vx planet,
                      y = y planet + dt * vy planet,
                      z = z planet + dt * vz planet} planet


energy : List a -> Float
energy planets = energy' 0.0 0

energy' : Float -> Integer -> Float
energy' e i = if i >= length planets
                 then return e
                 else do
                   p <- ( index i planets ) :- get
                   e1 <- energy'' p (i+1) e
                   e2 <- energy' e (i+1)
                   return $ e + 0.5 * mass p * squared (vx p) (vy p) (vz p)+e1+e2

energy'' : Planet -> Integer -> Float -> Float
energy'' p j e = if j >= length planets
                    then return e
                    else do
                      p <- ( index j planets ) :- get
                      let dx = the Float $ x pj - x p 
                      let dy = the Float $ y pj - y p 
                      let dz = the Float $ z pj - z p 
                      let distance = the Float $ sqrt $ squared dx dy dz 
                      e1 <- energy'' p (j+1) e
                      return $ e - (mass p * mass pj) / distance + e1


squared : Float -> Float -> Float -> Float
squared x y z = x * x + y * y + z * z

record Planet : Type where
    MKPlanet : (x: Float) ->
               (y: Float) ->
               (z: Float) ->
               (vx: Float) ->
               (vy: Float) ->
               (vz: Float) ->
               (mass: Float) -> Planet

solar_mass : Float
solar_mass = 4 * (pi `pow` 2)

dp : Float
dp = 365.24

dt : Float 
dt = 0.01

sun : Planet
sun = MKPlanet 0 0 0 0 0 0 solar_mass

jupiter : Planet
jupiter = MKPlanet x y z vx vy vz mass where
    x = 4.84143144246472090e+00
    y = -1.16032004402742839e+00
    z = -1.03622044471123109e-01
    vx = 1.66007664274403694e-03*dp
    vy = 7.69901118419740425e-03*dp
    vz = -6.90460016972063023e-05*dp
    mass = 9.54791938424326609e-04 * solar_mass

saturn : Planet
saturn = MKPlanet x y z vx vy vz mass where
    x = 8.34336671824457987e+00
    y = 4.12479856412430479e+00
    z = -4.03523417114321381e-01
    vx = -2.76742510726862411e-03*dp
    vy = 4.99852801234917238e-03*dp
    vz = 2.30417297573763929e-05*dp
    mass = 2.85885980666130812e-04 * solar_mass

uranus : Planet
uranus = MKPlanet x y z vx vy vz mass where
    x = 1.28943695621391310e+01
    y = -1.51111514016986312e+01
    z = -2.23307578892655734e-01
    vx = 2.96460137564761618e-03*dp
    vy = 2.37847173959480950e-03*dp
    vz = -2.96589568540237556e-05*dp
    mass = 4.36624404335156298e-05 * solar_mass

main : IO ()
main = do
    -- [_,a] <- getArgs
    -- let n = fromIntegerNat $ the Integer $ cast a -- (trim !getArgs)
    let n = the Nat $ 100

    let planets = map put [sun, jupiter, saturn, uranus, neptune]
  
    (head planets) :- update $ offsetMomentum $ init (0,0,0) 0 
    
    putStrLn $ show $ energy planets
    
    run n planets {- most of the action happens here -}
    
    putStrLn $ show $ energy planets
    return ()

