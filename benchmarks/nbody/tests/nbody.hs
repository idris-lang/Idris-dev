-- The Computer Language Benchmarks Game
-- http://benchmarksgame.alioth.debian.org/
--
-- Contributed by Branimir Maksimovic

import Foreign.Ptr
import Foreign.Storable
import Foreign.Marshal.Alloc
import Control.Monad
import System.Environment
import Text.Printf

main = do
    n <- getArgs >>= readIO.head :: IO Int
    pPlanets <- fromList planets
    nbodyInit pPlanets
    energy pPlanets >>= printf "%.9f\n" 
    run n pPlanets
    energy pPlanets >>= printf "%.9f\n" 

run 0 _ = return ()
run i p = do
        advance p
        run (i-1) p
        
data Planet = Planet { x,y,z,vx,vy,vz,mass :: !Double } deriving (Show)
    
offsetMomentum p (px,py,pz) = p {
                                   vx = -px / solar_mass,
                                   vy = -py / solar_mass,
                                   vz = -pz / solar_mass
                                }

nbodyInit pPlanets = do
    let init (px,py,pz) i = do
        if i < length planets
            then do
                p <- peekElemOff pPlanets i
                init (px + vx p * mass p,py + vy p * mass p, pz + vz p * mass p) (i+1)
            else return (px,py,pz)
    s <- init (0,0,0) 0
    p <- peek pPlanets
    poke pPlanets $ offsetMomentum p s

squared x y z = x * x + y * y + z * z
    
energy pPlanets = do
    let
        energy' e i = if i < length planets
                    then do
                        p <- peekElemOff pPlanets i
                        e1 <- energy'' p (i+1) e
                        e2 <- energy' e (i+1)
                        return $ e + 0.5 * mass p * squared (vx p) (vy p) (vz p)+e1+e2
                    else return e
        energy'' p j e = if j < length planets
                        then do
                            pj <- peekElemOff pPlanets j
                            let
                                distance = sqrt $ squared dx dy dz
                                dx = x pj - x p
                                dy = y pj - y p
                                dz = z pj - z p
                            e1 <- energy'' p (j+1) e
                            return $ e - (mass p * mass pj) / distance + e1
                        else return e
    energy' 0.0 0

advance pPlanets = do
    let 
        advance' i = 
            when (i < length planets) $ do
                    let
                        loop j = when (j < length planets) $ do
                                    ii <- peekElemOff pPlanets i
                                    jj <- peekElemOff pPlanets j
                                    let
                                        mag = dt / (dSquared * sqrt dSquared)
                                        dSquared = squared dx dy dz
                                        dx = x ii - x jj
                                        dy = y ii - y jj
                                        dz = z ii - z jj
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
                                    loop (j+1)
                    loop (i+1)
                    advance' (i+1)
        advance'' i = when (i < length planets) $ do
                            p <- peekElemOff pPlanets i
                            pokeC pPlanets i p { 
                                x = x p + dt * vx p,
                                y = y p + dt * vy p,
                                z = z p + dt * vz p
                                }
                            advance'' (i+1)
    advance' 0
    advance'' 0

planets = [sun, jupiter, saturn, uranus, neptune]
    
sun = Planet {x = 0, y = 0, z = 0,
              vx = 0, vy = 0, vz = 0,
              mass = solar_mass}
              
jupiter = Planet 
    {x = 4.84143144246472090e+00, y = -1.16032004402742839e+00, z= -1.03622044471123109e-01,
     vx = 1.66007664274403694e-03*dp, vy = 7.69901118419740425e-03*dp, vz = -6.90460016972063023e-05*dp,
     mass = 9.54791938424326609e-04 * solar_mass}

saturn = Planet
    { x = 8.34336671824457987e+00, y = 4.12479856412430479e+00, z = -4.03523417114321381e-01,
     vx = -2.76742510726862411e-03*dp,  vy = 4.99852801234917238e-03*dp, vz = 2.30417297573763929e-05*dp,
     mass = 2.85885980666130812e-04 * solar_mass}

uranus = Planet
    {x = 1.28943695621391310e+01,y = -1.51111514016986312e+01,z = -2.23307578892655734e-01,
     vx = 2.96460137564761618e-03*dp,vy = 2.37847173959480950e-03*dp, vz = -2.96589568540237556e-05*dp,
     mass = 4.36624404335156298e-05 * solar_mass}

neptune = Planet
    {x = 1.53796971148509165e+01,y = -2.59193146099879641e+01,z = 1.79258772950371181e-01,
     vx = 2.68067772490389322e-03*dp,vy = 1.62824170038242295e-03*dp, vz = -9.51592254519715870e-05*dp,
     mass = 5.15138902046611451e-05 * solar_mass}
     
days_per_year = 365.24
solar_mass    = 4 * pi ^ 2
dp = days_per_year
dt = 0.01

instance Storable Planet where
    sizeOf _ = 8 * dblSz
    alignment _ = dblSz
    peekElemOff p i = peek (plusPtr p (i * sizeOf (undefined::Planet)))
    pokeElemOff p i e = poke (plusPtr p (i * sizeOf e)) e
    peek p = do
        x <- peek (offset 0)
        y <- peek (offset 1)
        z <- peek (offset 2)
        vx <- peek (offset 3)
        vy <- peek (offset 4)
        vz <- peek (offset 5)
        mass <- peek (offset 6)
        return $ Planet {x=x,y=y,z=z,vx=vx,vy=vy,vz=vz,mass=mass}
            where
                offset i = plusPtr (castPtr p::Ptr Double) (i*8)
    poke p e = do
        poke (offset 0) $ x e
        poke (offset 1) $ y e
        poke (offset 2) $ z e
        poke (offset 3) $ vx e
        poke (offset 4) $ vy e
        poke (offset 5) $ vz e
        poke (offset 6) $ mass e
            where
                offset i = plusPtr (castPtr p::Ptr Double) (i*8)

dblSz = sizeOf (undefined::Double)

pokeC p i e = do
        poke (offset 0) $ x e
        poke (offset 1) $ y e
        poke (offset 2) $ z e
        where
            offset o = (plusPtr (castPtr p::Ptr Double)(o*8+i*64))

pokeV p i e = do
        poke (offset 3) $ vx e
        poke (offset 4) $ vy e
        poke (offset 5) $ vz e
        where
            offset o = (plusPtr (castPtr p::Ptr Double)(o*8+i*64))

fromList :: [Planet]->IO (Ptr Planet)
fromList l = do
    let len = length l
    pa <- mallocBytes (len * sizeOf (undefined::Planet))
    let 
        loop [] _ = return ()
        loop (x:xs) i = do
                            poke (pa `plusPtr` (i * sizeOf(undefined::Planet))) x
                            loop xs (i+1)
    loop l 0
    return pa
