#!/usr/bin/env bash

HEAD='module Main

strtake : Nat -> String -> String
strtake n str = pack (take n (unpack str))

getf : IO Double
getf = map cast getLine

main : IO ()'

# code separated from input with '#'
TESTS=('prim__floatToStr !getf#0.0'
 'prim__strToFloat !getLine#0.0'
$'prim__addFloat !getf !getf#1.0\n1.0'
$'prim__subFloat !getf !getf#1.0\n1.0'
$'prim__mulFloat !getf !getf#1.0\n1.0'
$'prim__divFloat !getf !getf#1.0\n1.0'
$'prim__slteFloat !getf !getf#1.0\n1.0'
$'prim__sltFloat !getf !getf#1.0\n1.0'
$'prim__sgteFloat !getf !getf#1.0\n1.0'
$'prim__sgtFloat !getf !getf#1.0\n1.0'
$'prim__eqFloat !getf !getf#1.0\n1.0'
 'prim__floatACos !getf#1.0'
 'prim__floatATan !getf#1.0'
 'prim__floatCos !getf#1.0'
 'prim__floatFloor !getf#1.0'
 'prim__floatSin !getf#1.0'
 'prim__floatTan !getf#1.0'
 'prim__floatASin !getf#1.0'
 'prim__floatCeil !getf#1.0'
 'prim__floatExp !getf#1.0'
 'prim__floatLog !getf#1.0'
 'prim__floatSqrt !getf#1.0'
 'prim__negFloat !getf#1.0'
)

generate_testfile()
{
cat <<EOF > $1
${HEAD}
main = putStrLn $ strtake 10 (show $ $2)
EOF
}

for T in "${TESTS[@]}"
do
    echo ${T%% *} ${T##*#}
    generate_testfile "tmptest.idr" "${T%%#*}"
    ${IDRIS:-idris} $@ --quiet --port none tmptest.idr -o tmptest || echo "missing primitive in ${CG}"
    ./tmptest <<<"${T##*#}"
    rm tmptest.idr tmptest.ibc tmptest
done
