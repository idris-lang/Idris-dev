module Main

import Data.Float
import Data.Vect
import Data.Fin
import System 
import Effects
import Effect.State
import Effect.StdIO

data Point = MkPoint (Vect 3 Float)
instance Default Point where
    default = MkPoint [0,0,0]

data Velocity = MkVelocity (Vect 3 Float)
instance Default Velocity where
    default = MkVelocity [0,0,0]

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



offsetMomentum : Vect 5 Velocity -> Velocity
offsetMomentum vs = foldr velAdd (MkVelocity [0,0,0]) $ zipWith scMulV masses vs

velAdd : Velocity -> Velocity -> Velocity
velAdd (MkVelocity vct1) (MkVelocity vct2) = MkVelocity [| vct1 + vct2 |]

velSub : Velocity -> Velocity -> Velocity
velSub (MkVelocity vct1) (MkVelocity vct2) = MkVelocity [| vct1 - vct2 |]

scMulV : Float -> Velocity -> Velocity
scMulV s (MkVelocity vct) = MkVelocity $ map (*s) vct 

scMulP : Float -> Point -> Point
scMulP s (MkPoint vct) = MkPoint $ map (*s) vct 

nbodyInit : Vect 5 Velocity -> Velocity
nbodyInit vs = scMulV (-1/solar_mass) $ offsetMomentum vs

velMag : Velocity -> Float
velMag (MkVelocity vct) = foldr (+) 0 $ map (pow 2) vct

poiMag : Point -> Float
poiMag (MkPoint vct) = foldr (+) 0 $ map (pow 2) vct

poiSub : Point -> Point -> Point
poiSub = (MkPoint vct1) (MkPoint vct2) = MkPoint [| vct1 - vct2 |]

poiAdd : Point -> Point -> Point
poiAdd = (MkPoint vct1) (MkPoint vct2) = MkPoint [| vct1 + vct2 |]

energy : Vect n Point -> Vect n Velocity -> Float
energy ps vs = sum $ map energy' [ (i, j) | j <- [0..n-1], i <- [0..n-1], i <= j ] where
    energy' (i, j) = index i masses * if i == j {- the ( (Fin n, Fin n) -> Float ) $ -}
        then velMag (index i vs) / 2
        else index j masses / -distance where 
            distance = sqrt $ poiMag $ (index i ps) `poiSub` (index j ps)


{-
advance : (Vect n Point, Vect n Velocity) -> (Vect n Point, Vect n Velocity) 
advance (ps, vs) = (map MoveBody ps)
map advance' [ (i, j) | j <- [0..n-1], i <- [0..n-1], i < j ] 
let advance' (i, j) = 




                    let dv = (index i vs) `poiSub` (index j vs)
                    let mag = dt / (dMag * sqrt dMag) where dMag = poiMag dv in
                    let point 
                    scMulV (mag * index j masses) dv 
                                    pokeV pPlanets i ii{
                                        vx = vx ii - dx * mass jj * mag,
                                        vy = vy ii - dy * mass jj * mag,
                                        vz = vz ii - dz * mass jj * mag
                                        }
                                    pokeV pPlanets j jj{
                                        vx = vx jj + dx * mass ii * mag,
                                        vy = vy jj + dy * mass ii * mag,
                                        vz = vz jj + dz * mass ii * mag
                                        }
let dSquared = poiMag v_i `poiSub` v_j
let v_j = index j vs
let v_i = index i vs

accel : (Fin 5, Fin 5) -> Velocity
accel (i, j) = let dv = (index i vsTags :- get) `poiSub` (index j vsTags :- get) in
               let mag = dt / (dMag * sqrt dMag) where dMag = poiMag dv in
               scMulV (mag * index j masses) dv
    
incrementTag : Int -> {['Tag ::: STATE Int ]} Eff ()
incrementTag i = 'Tag :- update (\x => x + i)
-}

-- accel : Velocity -> Velocity -> Float -> Velocity 


advance : {[ 'SunV ::: STATE Velocity, 'SunP ::: STATE Point,
          'JupiterV ::: STATE Velocity, 'JupiterP ::: STATE Point,
          'SaturnV ::: STATE Velocity,'SaturnP ::: STATE Point,
          'UranusV ::: STATE Velocity,'UranusP ::: STATE Point,
          'NeptuneV ::: STATE Velocity, 'NeptuneP ::: STATE Point ]} Eff ()
advance = let vsTags = the (Vect 5 Type) ['SunV, 'JupiterV, 'SaturnV, 'UranusV, 'NeptuneV] in 
          let psTags = the (Vect 5 Type) ['SunP, 'JupiterP, 'SaturnP, 'UranusP, 'NeptuneP] in
          let accel p_i p_j m_j = let dp = p_i `poiSub` p_j in 
                    let mag = dt / (dMag * sqrt dMag) where dMag = poiMag dp in 
                    scMulV (mag * m_j) dv
          let pointPair (i,j) = let viT = index i vsTags in 
                                let vjT = index j vsTags in 
                                let piT = index i psTags in 
                                let pjT = index j psTags in 
                                let pointVel = accel (piT :- get) (pjT :- get) (index j masses) in 
                                do viT :- update $ velSub pointVel 
                                   vjT :- update $ velAdd pointVel in
          let moveBody i = let piT = index i psTags in
                           let vit = index i vsTags in
                           let move = poiAdd (MkPoint vct) where MkVelocity vct = scMulV dt (viT :- get) in
                           do piT :- update move 
          do map pointPair [ (i, j) | j <- [0..4], i <- [0..4], i < j ]
             map moveBody [0..4]

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
nbody n = do
    'SunV :- put $ nbodyInit [  !('SunV :- get),
                                !('JupiterV :- get),
                                !('SaturnV :- get),
                                !('UranusV :- get),
                                !('NeptuneV :- get) ]
    let initialEnergy = energy [!('SunP :- get), 
                                !('JupiterP :- get),
                                !('SaturnP :- get),
                                !('UranusP :- get),
                                !('NeptuneP :- get) ] 
                               [!('SunV :- get),
                                !('JupiterV :- get),
                                !('SaturnV :- get),
                                !('UranusV :- get),
                                !('NeptuneV :- get) ]
    --
    (foldr1 (.) $ replicate n advance)([!('SunP :- get), 
                                        !('JupiterP :- get),
                                        !('SaturnP :- get),
                                        !('UranusP :- get),
                                        !('NeptuneP :- get) ],  
                                       [!('SunV :- get),
                                        !('JupiterV :- get),
                                        !('SaturnV :- get),
                                        !('UranusV :- get),
                                        !('NeptuneV :- get) ] )



main : IO ()
main = do 
  (_ :: arg :: _) <- getArgs
  let n = fromIntegerNat $ the Integer $ cast arg

  let energies = runPureInit [
               'SunP := MkPoint [0,0,0], 
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
    map printLn energies


-- ['SunV, 'JupiterV, 'SaturnV, 'UranusV, 'NeptuneV ]
  -- [!('SunV :- get), !('JupiterV :- get), !('SaturnV :- get), !('UranusV :- get), !('NeptuneV :- get) ]
  -- ['SunP, 'JupiterP, 'SaturnP, 'UranusP, 'NeptuneP ]
  -- [!('SunP :- get), !('JupiterP :- get), !('SaturnP :- get), !('UranusP :- get), !('NeptuneP :- get) ]

  -- nbodyInit
