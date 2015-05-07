module Main

import Effect.StdIO
import Data.Floats

main : IO ()
main = do
    let n = cast (trim !getStr)
    nbodyInit planets
    putStrLn $ energy planets
    run n planets
    putStrLn $ energy planets
  
run 0 _ = return ()
run i p = do
    advance p
    run (i-1) p

record Planet : Type where
    MKPlanet : (x: Float) ->
               (y: Float) ->
               (z: Float) ->
               (vx: Float) ->
               (vy: Float) ->
               (vz: Float) ->
               (mass: Float) -> Planet

offsetMomentum p (px,py,pz) = record { vx = -px / solar_mass, vy = -py / solar_mass, vz = -pz / solar_mass } p

squared x y z = x * x + y * y + z * z

nbodyInit planets = do
    let init (px,py,pz) i = do
        if i >= length planets
            then return (px,py,pz)
            else do
                let p = planets !! i
                init (px + vx p * mass p, py + vy p * mass p, pz + vz p * mass p) (i+1)
    s <- init (0,0,0) 0
    p <- peek pPlanets
    poke pPlanets $ offsetMomentum p s
    
energy planets = do


advance planets = do




planets : List Planet
planets = [sun, jupiter, saturn, uranus, neptune]

jupiter = MKPlanet x y z vx vy vz mass where
    x = 4.84143144246472090e+00
    y = -1.16032004402742839e+00
    z = -1.03622044471123109e-01
    vx = 1.66007664274403694e-03*dp
    vy = 7.69901118419740425e-03*dp
    vz = -6.90460016972063023e-05*dp
    mass = 9.54791938424326609e-04 * solar_mass

saturn = MKPlanet x y z vx vy vz mass where
    x = 8.34336671824457987e+00
    y = 4.12479856412430479e+00
    z = -4.03523417114321381e-01
    vx = -2.76742510726862411e-03*dp
    vy = 4.99852801234917238e-03*dp
    vz = 2.30417297573763929e-05*dp
    mass = 2.85885980666130812e-04 * solar_mass

uranus = MKPlanet x y z vx vy vz mass where
    x = 1.28943695621391310e+01
    y = -1.51111514016986312e+01
    z = -2.23307578892655734e-01
    vx = 2.96460137564761618e-03*dp
    vy = 2.37847173959480950e-03*dp
    vz = -2.96589568540237556e-05*dp
    mass = 4.36624404335156298e-05 * solar_mass

neptune = MKPlanet x y z vx vy vz mass where
    x = 1.53796971148509165e+01
    y = -2.59193146099879641e+01
    z = 1.79258772950371181e-01
    vx = 2.68067772490389322e-03*dp
    vy = 1.62824170038242295e-03*dp
    vz = -9.51592254519715870e-05*dp
    mass = 5.15138902046611451e-05 * solar_mass

sun = MKPlanet 0 0 0 0 0 0 solar_mass

solar_mass : Float
solar_mass = 4 * pi ^ 2
dp = 365.24
dt = 0.01
