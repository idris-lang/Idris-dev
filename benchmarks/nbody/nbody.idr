module Main

import System 
import Effects
import Effect.State
import Effect.StdIO
import Data.Float
import Data.Vect
import Data.Fin

Velocity : Type
Velocity = Vect 3 Float

Position : Type
Position = Vect 3 Float


(/+\) xs ys = 

dt : Float
dt = 0.01

dp : Float
dp = 365.24

solar_mass : Float
solar_mass = 4 * (pi `pow` 2)

masses : Vect 5 Float
masses = [ solar_mass,
         9.54791938424326609e-04*solar_mass,  -- jupiter
         2.85885980666130812e-04*solar_mass,  -- saturn
         4.36624404335156298e-05*solar_mass,  -- uranus
         5.15138902046611451e-05*solar_mass ] -- neptune


nbodyInit : Vect 4 Velocity -> {[ 'SunV ::: STATE Velocity ]} Eff ()
nbodyInit vs = 

nbody : Nat -> {[ 'SunV ::: STATE Velocity, 'SunP ::: STATE Position,
               'JupiterV ::: STATE Velocity, 'JupiterP ::: STATE Position,
               'SaturnV ::: STATE Velocity, 'SaturnP ::: STATE Position,
               'UranusV ::: STATE Velocity, 'UranusP ::: STATE Position,
               'NeptuneV ::: STATE Velocity, 'NeptuneP ::: STATE Position ]} 
               Eff (Vect 2 Float)
nbody n = do
  nbodyInit
  let initialEnergy = energy ?Planetarium
  advance n
  let finalEnergy = energy ?Planetarium
  pure [initialEnergy, finalEnergy]

main : IO ()
main = do 
  (_ :: arg :: _) <- getArgs
  let n = fromIntegerNat $ the Integer $ cast arg

  let energies = runPureInit [
               'SunP := [0,0,0], 
               'SunV := [0,0,0],
               'JupiterP := [ 4.84143144246472090e+00,
                            -1.16032004402742839e+00,
                            -1.03622044471123109e-01 ],
               'JupiterV := [ 1.66007664274403694e-03*dp,
                            7.69901118419740425e-03*dp,
                            -6.90460016972063023e-05*dp ],
               'SaturnP := [ 8.34336671824457987e+00,
                           4.12479856412430479e+00,
                           -4.03523417114321381e-01 ],
               'SaturnV := [ -2.76742510726862411e-03*dp,
                           4.99852801234917238e-03*dp,
                           2.30417297573763929e-05*dp ],
               'UranusP := [ 1.28943695621391310e+01,
                           -1.51111514016986312e+01,
                           -2.23307578892655734e-01 ],
               'UranusV := [ 2.96460137564761618e-03*dp,
                           2.37847173959480950e-03*dp,
                           -2.96589568540237556e-05*dp ],
               'NeptuneP := [ 1.53796971148509165e+01,
                           -2.59193146099879641e+01,
                           1.79258772950371181e-01 ],
               'NeptuneV := [ 2.68067772490389322e-03*dp,
                            1.62824170038242295e-03*dp,
                            -9.51592254519715870e-05*dp ]
                             ] (nbody n)
    map printLn energies



