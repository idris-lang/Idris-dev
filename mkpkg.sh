#!/bin/sh

VERSION=$1

echo "Building version-$VERSION\n\n"
echo "Have you: set the release flag, checked the demos and the tutorial?"
read $foo

git tag v$VERSION -a

cabal sdist

# Generate Idris library docs and put them in lib_docs.tar.gz in the root
make lib_doc
DOCDIR=`mktemp -d /tmp/docsXXXXX`
cp -r libs/base/base_doc "$DOCDIR"
cp -r libs/prelude/prelude_doc "$DOCDIR"
cp -r libs/effects/effects_doc "$DOCDIR"
cp -r libs/contrib/contrib_doc "$DOCDIR"
tar -czvf lib_docs.tar.gz -C "$DOCDIR" prelude_doc base_doc effects_doc contrib_doc

cabal configure --prefix=/usr/local
cabal build
cabal copy --destdir=/tmp/idris-pkg/
pkgbuild --id org.idris-lang --root /tmp/idris-pkg/ idris-$VERSION.pkg 

