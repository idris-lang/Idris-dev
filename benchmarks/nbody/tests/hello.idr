module Main

import Effect.StdIO
import Data.Floats

solar_mass : Float
solar_mass = 4 * (pi `pow` 2)

record Planet : Type where
    MKPlanet : (x: Float) ->
               (y: Float) ->
               (z: Float) ->
               (vx: Float) ->
               (vy: Float) ->
               (vz: Float) ->
               (mass: Float) -> Planet

main : IO ()
main = putStrLn $ the String $ cast $ x $ move sun

move : a -> a
move planet = record{ x = x planet + dt * vx planet,
                      y = y planet + dt * vy planet,
                      z = z planet + dt * vz planet} planet

dt : Float 
dt = 0.01

-- n : Float
-- n = cast (trim !getStr)

sun : a
sun = MKPlanet 0 0 0 0 0 0 solar_mass


{- planets : List Planet -}
{- FIXME: IMPLEMENT -----> advance -}
{-


-- let (MkVelocity [px, py, pz]) = v
-- let p = index i planets
-- let mass = m p
-- (MkVelocity [vx, vy, vz]) <- (vs p)
-- let MkVelocity [vx, vy, vz] = !get -- (vs p)
-- offsetMomentum' (succ i) $ offsetMomentum'' v p where p = index i planets



{-
offsetMomentum' : Fin ix -> Velocity -> Velocity
offsetMomentum' i v = if (i == (fromNat ix))
                         then v
                         else offsetMomentum''' i v

offsetMomentum'' : Velocity -> Body -> Velocity
offsetMomentum'' (MkVelocity [px, py, pz]) p = let MkVelocity [vx, vy, vz] = getVelocity p in
                                                   MkVelocity [px + vx * m p, 
                                                              py + vy * m p, 
                                                              pz + vz * m p ] 

offsetMomentum''' : Fin ix -> Velocity -> Velocity
offsetMomentum''' i v = offsetMomentum' (succ i) $ offsetMomentum'' v (index i planets)



offsetMomentum'' : Velocity -> Body -> Velocity
offsetMomentum'' (MkVelocity [px, py, pz]) p = let (MkVelocity [vx, vy, vz]) = (getVelocity' p) in
                                                  let mass = m p in
                                                  MkVelocity [px + vx * mass, 
                                                              py + vy * mass, 
                                                              pz + vz * mass ] 

getVelocity : Body -> Velocity
getVelocity p = runPure $ do
  do v' <- vs p
     pure v'

unState : a -> b
unState getter statefulValue = runPure $ do (pure !(getter statefulValue))

offsetMomentum : Float -> Velocity -> Velocity
offsetMomentum m (MkVelocity [vx, vy, vz]) = MkVelocity [-vx/m, -vy/m, -vz/m]
-}

offsetMomentum'' (length planets) v = v
offsetMomentum'' (length planets + n) v = offsetMomentum''' (length planets + n) v

offsetMomentum''' i v = run $ do 
  let (MkVelocity [px, py pz]) = v
  let p = index i planets
  let mass = m p
  (MkVelocity [vx, vy vz]) <- (vs p) :- get
  offsetMomentum''' (FS i) $ MkVelocity [px + vx * mass, 
                                         py + vy * mass, 
                                         pz + vz * mass ]


{-
energy : Vect 5 Point -> Vect 5 Velocity -> Float
energy ps vs = foldr (+) 0 $ 
    where 
        e3 = index ii masses * index jj masses / -distance
        distance = sqrt $ poiMag dp
        dp = map disPot [ (x, y) | y <- [0..4], x <- [0..4], x < y ]
        disPot (ii, jj) = if ii == jj 
            then e4 + (index ii masses) * velMag (index ii vs) / 2 -- other behabior 
            else e4 
            where e4 = poiSub (index ii ps) (index jj ps)
        energy' vs ps (ii, jj) = poiSub (index ii ps) (index jj ps)
foldr (+) 0 $ zipWith3 ?MysteryFunc? ps vs masses
  where ?MystertFunc? p v m = m * velMag v / 2.0
  + energy'' p (i+1) e + energy' e (i+1)
  combinations = [ (x, y) | y <- [1..5], x <- [1..5], x < y ]


energy planets = fold (+) 0 $ planetsEnergy ++ pairsEnergy
    where
        planetsEnergy : List Float
        planetsEnergy = map energysList planets
        
        pairsEnergy : List Float
        pairsEnergy combinations = map energyPair combinations
        
        energyPair : (Planet, Planet) -> Float
        energyPair (planet_1, planet_2) = -(mass planet_1 * mass planet_2) / distance
            where
                distance : Float
                distance = sqrt $ squared dx dy dz
                    where
                        dx = x planet_1 - x planet_2
                        dy = y planet_1 - y planet_2
                        dz = z planet_1 - z planet_2
        
        energysList : Planet -> Float
        energysList planet = m * norm / 2
            where
                m = mass planet
                norm = squared (vx planet) (vy planet) (vz planet) 
-}

energy planets = map (+) $ planetsEnergy ++ pairsEnergy
    where
        planetsEnergy : List Float
        planetsEnergy = map energysList planets
        
        pairsEnergy : List Float
        pairsEnergy combinations = map energyPair combinations
        
        energyPair : (Planet, Planet) -> Float
        energyPair (planet_1, planet_2) = -(mass planet_1 * mass planet_2) / distance
            where
                distance : Float
                distance = sqrt $ squared dx dy dz
                    where
                        dx = x planet_1 - x planet_2
                        dy = y planet_1 - y planet_2
                        dz = z planet_1 - z planet_2
        
        energysList : Planet -> Float
        energysList planet = m * norm / 2
            where
                m = mass planet
                norm = squared (vx planet) (vy planet) (vz planet) 

combinations : List (Planet, Planet) {- LazyList maybie? -}
combinations = [ (get x, get y) | y <- planets, x <- planets, not $ x == y ]
{- combinations = [ (place x , place y) | z <- planets, y <- planets, not $ x == y ] 
                where place n = (!!0) $ elemIndices n planets-}

advance planets : List { [STATE Planet] } Eff m () -> IO ()
advance planets = let
    updatePairsVelocity = do 
        map calculatePairsVelocities combinations
            where
                calculatePairsVelocities (planet_1, planet_2) = do
                    let dx = x planet_1 - x planet_2
                    let dy = y planet_1 - y planet_2
                    let dz = z planet_1 - z planet_2
                    let magnitude = dt * ( (squared dx dy dz) ** (-3/2) )
                    let new_planet_1 = record { vx = vx planet_1 - dx * b1m, 
                                                vy = vy planet_1 - dy * b1m, 
                                                vz = vz planet_1 - dz * b1m } planet_1 
                                                    where b1m = mass planet_1 * magnitude
                    let new_planet_2 = record { vx = vx planet_2 + dx * b2m, 
                                                vy = vy planet_2 + dy * b2m, 
                                                vz = vz planet_2 + dz * b2m, } planet_2 
                                                    where b2m = mass planet_2 * magnitude
                    update new_planet_1 old_planet_1 
                        where old_planet_1 = Just planet_1 == get {- first in combinations -}
                    update new_planet_2 old_planet_2 {- second in combinations : elemIndex :: Eq a => a -> [a] -> Maybe Int-}
    updatePlanetsPosition = do
        map movePlanets planets
    
    in do
        updatePairsVelocity
        updatePlanetsPosition
        
    {- [_,a] <- getArgs
    let n = fromIntegerNat (the Integer (cast a)) -}
-}

{- let planets = the ( Vect 5 { [STATE Planet] } Eff m () ) $ map put [sun, jupiter, saturn, uranus, neptune]
      sunE :- update $ offsetMomentum $ init (0,0,0) 0 where
      sunE : { [STATE Planet] } Eff m ()
      sunE = head planets

    -}
