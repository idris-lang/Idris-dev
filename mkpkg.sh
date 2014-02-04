#!/bin/sh

echo "Building version-$VERSION\n\n"
echo "Have you: set the release flag, checked the demos and the tutorial?"
read $foo

git tag version-$VERSION -a

VERSION=$1

cabal sdist

cabal configure --prefix=/usr/local
cabal build
cabal copy --destdir=/tmp/idris-pkg/
pkgbuild --id org.idris-lang --root /tmp/idris-pkg/ idris-$VERSION.pkg 

