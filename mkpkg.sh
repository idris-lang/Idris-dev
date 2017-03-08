#!/usr/bin/env sh

set -euo pipefail

if [ "$#" -lt 1 ]; then
    echo "Usage $0 [version number] ?[idris bin location]"
    echo ""
    echo "The first argument is the version number"
    echo ""
    echo "The second argument is optional, and used to point to a"
    echo "custom location in which idris was recently built i.e."
    echo "withing .stack-work or .cabal-sandbox. The location must"
    echo "be given relative to the project root of a package in the "
    echo "libs/ directory."
    exit 1
fi

VERSION=${1:-}

echo "==> Building version-$VERSION"
echo ""
echo "Q: Have you: (a) set the release flag & (b) checked the demos and the tutorial?"
read ${FOO:-}

git tag v$VERSION -a

echo "==> Building Source Distribution"
cabal sdist

# Generate Idris library docs and put them in lib_docs.tar.gz in the root
echo "==> Generating API Documentation."
echo "==> Determining version of Idris to use."
if [ -z ${2+x} ];
then
    echo "==> Using default location.";
    make lib_doc
else
    echo "==> Using custom location.";
    make -C libs IDRIS=$2 doc
fi

DOCDIR=`mktemp -d /tmp/docsXXXXX`

cp -r libs/base/base_doc "$DOCDIR"
cp -r libs/prelude/prelude_doc "$DOCDIR"
cp -r libs/effects/effects_doc "$DOCDIR"
cp -r libs/contrib/contrib_doc "$DOCDIR"

tar -czvf lib_docs.tar.gz -C "$DOCDIR" prelude_doc base_doc effects_doc contrib_doc

echo "==> Building Binaries"
cabal configure --prefix=/usr/local

cabal build

echo "==> Creating Package"
mkdir -p /tmp/idris-pkg/

cabal copy --destdir=/tmp/idris-pkg/

pkgbuild --identifier org.idris-lang \
         --version "v$VERSION"       \
         --root /tmp/idris-pkg/      \
         idris-$VERSION.pkg

echo "==> Creating SHA256 hash (don't forget to update web site!)"
shasum -a 256 idris-$VERSION.pkg > idris-$VERSION.pkg.sha256
