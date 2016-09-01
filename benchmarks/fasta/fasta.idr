module Main

import System

alu : String
alu = "GGCCGGGCGCGGTGGCTCACGCCTGTAATCCCAGCACTTTGGGAGGCCGAGGCGGGCGGATCACCTGAGG\
    \TCAGGAGTTCGAGACCAGCCTGGCCAACATGGTGAAACCCCGTCTCTACTAAAAATACAAAAATTAGCCGGG\
    \CGTGGTGGCGCGCGCCTGTAATCCCAGCTACTCGGGAGGCTGAGGCAGGAGAATCGCTTGAACCCGGGAGGC\
    \GGAGGTTGCAGTGAGCCGAGATCGCGCCACTGCACTCCAGCCTGGGCGACAGAGCGAGACTCCGTCTCAAAAA"

iub : List (Char, Double)
iub = [('a',0.27),('c',0.12),('g',0.12),('t',0.27),('B',0.02)
      ,('D',0.02),('H',0.02),('K',0.02),('M',0.02),('N',0.02)
      ,('R',0.02),('S',0.02),('V',0.02),('W',0.02),('Y',0.02)]

homosapiens : List (Char, Double)
homosapiens = [('a',0.3029549426680),('c',0.1979883004921)
              ,('g',0.1975473066391),('t',0.3015094502008)]


takeRepeat : Int -> String -> String
takeRepeat n s = if n > m
                 then s ++ takeRepeat (n-m) s
                 else pack $ take (cast n) $ unpack s
  where
    m = cast $ length s

splitAt' : Nat -> String -> (String, String)
splitAt' n s = let s' = unpack s in (pack $ take n s', pack $ drop n s')

writeAlu : String -> String -> IO ()
writeAlu name s0 = putStrLn name *> go s0
  where
    go "" = pure ()
    go s  = let (h,t) = splitAt' 60 s in putStrLn h *> go t

replicate : Int -> Char -> String
replicate 0 c = ""
replicate n c = singleton c <+> replicate (n-1) c

scanl : (f : acc -> a -> acc) -> acc -> List a -> List acc
scanl f q ls = q :: (case ls of
                        []    => []
                        x::xs => scanl f (f q x) xs)

accum : (Char,Double) -> (Char,Double) -> (Char,Double)
accum (_,p) (c,q) = (c,p+q)

make : String -> Int -> List (Char, Double) -> Int -> IO Int
make name n0 tbl seed0 = do
    putStrLn name
    make' n0 0 seed0 ""
  where
    modulus : Int
    modulus = 139968

    fill : List (Char,Double) -> Int -> List String
    fill ((c,p) :: cps) j =
      let k = min modulus (cast (cast modulus * p + 1))
      in replicate (k - j) c :: fill cps k
    fill _ _ = []

    lookupTable : String
    lookupTable = Foldable.concat (fill (scanl accum ('a',0) tbl) 0)

    make' : Int -> Int -> Int -> String -> IO Int
    make' 0 col seed buf = when (col > 0) (putStrLn buf) *> pure seed
    make' n col seed buf = do
      let newseed  = modInt (seed * 3877 + 29573) modulus
      let nextchar = strIndex lookupTable newseed
      let newbuf   = buf <+> singleton nextchar
      if col+1 >= 60
        then putStrLn newbuf *> make' (n-1) 0 newseed ""
        else make' (n-1) (col+1) newseed newbuf


main : IO ()
main = do
    (_ :: n :: _) <- getArgs
    writeAlu ">ONE Homo sapiens alu" (takeRepeat (fromInteger (cast n)*2) alu)
    nseed <- make ">TWO IUB ambiguity codes" (fromInteger (cast n)*3) iub 42
    make ">THREE Homo sapiens frequency" (fromInteger (cast n)*5) homosapiens nseed
    pure ()
