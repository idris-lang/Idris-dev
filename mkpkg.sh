#!/bin/sh

VERSION=$1

echo "Building version-$VERSION\n\n"
echo "Have you: set the release flag, checked the demos and the tutorial?"
read $foo

git tag v$VERSION -a

cabal sdist

cabal configure --prefix=/usr/local
cabal build
cabal copy --destdir=/tmp/idris-pkg/
pkgbuild --id org.idris-lang --root /tmp/idris-pkg/ idris-$VERSION.pkg 

