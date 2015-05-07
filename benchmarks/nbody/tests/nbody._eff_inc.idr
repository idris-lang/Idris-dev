module Main
-- Author: Har'el Fishbein
-- N body problem benchmark

import System
import Effects
import Effect.State
import Effect.StdIO
import Data.Fin
import Data.Vect
import Data.Vect.Quantifiers
import Decidable.Equality
import Data.Floats

data Point = MkPoint (Vect 3 Float)
instance Default Point where
    default = MkPoint [0,0,0]

data Velocity = MkVelocity (Vect 3 Float)
instance Default Velocity where
    default = MkVelocity [0,0,0]

record Body : Type where
    MkBody : (ps: { [STATE Point] } Eff Point ) ->
             (vs: { [STATE Velocity] } Eff Velocity ) ->
                  (m: Float) -> Body

MkPlanet : Float -> Float -> Float ->
           Float -> Float -> Float ->
           Float -> Body
MkPlanet x y z vx vy vz m = MkBody
                            (pure $ MkPoint [x, z, y])
                            (pure $ MkVelocity [vx, vy, vz])
                            m



dt : Float
dt = 0.01

dp : Float
dp = 365.24

solar_mass : Float
solar_mass = 4 * (pi `pow` 2)

sun : Body
sun = MkPlanet x y z vx vy vz mass where
  x = 0
  y = 0
  z = 0
  vx = 0
  vy = 0
  vz = 0
  mass = 0

jupiter : Body
jupiter = MkPlanet x y z vx vy vz mass where
  x = 4.84143144246472090e+00
  y = -1.16032004402742839e+00
  z = -1.03622044471123109e-01
  vx = 1.66007664274403694e-03*dp
  vy = 7.69901118419740425e-03*dp
  vz = -6.90460016972063023e-05*dp
  mass = 9.54791938424326609e-04*solar_mass

saturn : Body
saturn = MkPlanet x y z vx vy vz mass where
  x = 8.34336671824457987e+00
  y = 4.12479856412430479e+00
  z = -4.03523417114321381e-01
  vx = -2.76742510726862411e-03*dp
  vy = 4.99852801234917238e-03*dp
  vz = 2.30417297573763929e-05*dp
  mass = 2.85885980666130812e-04*solar_mass

uranus : Body
uranus = MkPlanet x y z vx vy vz mass where
  x = 1.28943695621391310e+01
  y = -1.51111514016986312e+01
  z = -2.23307578892655734e-01
  vx = 2.96460137564761618e-03*dp
  vy = 2.37847173959480950e-03*dp
  vz = -2.96589568540237556e-05*dp
  mass = 4.36624404335156298e-05*solar_mass

neptune : Body
neptune = MkPlanet x y z vx vy vz mass where
  x = 1.53796971148509165e+01
  y = -2.59193146099879641e+01
  z = 1.79258772950371181e-01
  vx = 2.68067772490389322e-03*dp
  vy = 1.62824170038242295e-03*dp
  vz = -9.51592254519715870e-05*dp
  mass = 5.15138902046611451e-05*solar_mass

planets : Vect 5 Body
planets = [sun, jupiter, saturn, uranus, neptune]

ix : Nat
ix = length planets

getVelocity : Body -> Velocity
getVelocity p = runPure $ do (pure !(vs p) )

offsetMomentum : Fin ix -> Velocity -> Velocity
offsetMomentum i v = if (i == (fromNat ix))
                        then v
                        else offsetMomentum (succ i) $ let MkVelocity [px, py, pz] = v in
                                                       let p = index i planets in
                                                       let MkVelocity [vx, vy, vz] = getVelocity p in
                                                       let mass = m p in MkVelocity [px + vx * mass,
                                                                                    py + vy * mass,
                                                                                    pz + vz * mass ]



--nbodyInit : Body -> IO ()
--nbodyInit p = do
--  (vs p) :- update $ (offsetMomentum' $ m p) . (offsetMomentum 0)


test_ofstmtm : Velocity
test_ofstmtm = (getVelocity sun)

main : IO ()
main = do -- run [ sun_i := head planets] $ do
  (_ :: arg :: _) <- getArgs
  let n = fromIntegerNat $ the Integer $ cast arg

  runPureInit ['SunP := MkPoint [0,0,0],
               'SunV := MkVelocity [0,0,0],
               'JupiterP := MkPoint [ 4.84143144246472090e+00,
                                     -1.16032004402742839e+00,
                                     -1.03622044471123109e-01 ],
               'JupiterV := MkVelocity [ 1.66007664274403694e-03*dp,
                                       7.69901118419740425e-03*dp,
                                       -6.90460016972063023e-05*dp ],
               'SaturnP := MkPoint [ 8.34336671824457987e+00,
                                    4.12479856412430479e+00,
                                    -4.03523417114321381e-01 ],
               'SaturnV := MkPoint [ -2.76742510726862411e-03*dp,
                                    4.99852801234917238e-03*dp,
                                    2.30417297573763929e-05*dp ],
               'UranusP := MkPoint [ 1.28943695621391310e+01,
                                    -1.51111514016986312e+01,
                                    -2.23307578892655734e-01 ],
               'UranusV := MkVelocity [ 2.96460137564761618e-03*dp,
                                      2.37847173959480950e-03*dp,
                                      -2.96589568540237556e-05*dp ],
               'NeptuneP := MkPoint [ 1.53796971148509165e+01,
                                    -2.59193146099879641e+01,
                                    1.79258772950371181e-01 ],
               'NeptuneV := MkVelocity [ 2.68067772490389322e-03*dp,
                                       1.62824170038242295e-03*dp,
                                       -9.51592254519715870e-05*dp ]
                             ] (nbody n)
  -- let v = getVelocity saturn
  
  printLn $ m neptune


nbody : Nat ->
        {[ 'SunV ::: STATE Velocity,
           'SunP ::: STATE Point,
           'JupiterV ::: STATE Velocity,
           'JupiterP ::: STATE Point,
           'SaturnV ::: STATE Velocity,
           'SaturnP ::: STATE Point,
           'UranusV ::: STATE Velocity,
           'UranusP ::: STATE Point,
           'NeptuneV ::: STATE Velocity,
           'NeptuneP ::: STATE Point ]} Eff $ List Float
nbody = do
  -- ['SunV, 'JupiterV, 'SaturnV, 'UranusV, 'NeptuneV ]
  -- ['SunP, 'JupiterP, 'SaturnP, 'UranusP, 'NeptuneP ]
  'SunV :- put
  

-- fpow f n = foldr (.) (take n $ repeat f)

